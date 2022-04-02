#!/usr/bin/env python3
# mmverify.py -- Proof verifier for the Metamath language
# Copyright (C) 2002 Raph Levien raph (at) acm (dot) org
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License

# To run the program, type
#   $ python3 mmverify.py set.mm --logfile set.log
# or (using bash redirections)
#   $ python3 mmverify.py < set.mm 2> set.log
# and set.log will have the verification results.
# To get help on the program usage, type
#   $ python3 mmverify.py -h

# (nm 27-Jun-2005) mmverify.py requires that a $f hypothesis must not occur
# after a $e hypothesis in the same scope, even though this is allowed by
# the Metamath spec.  This is not a serious limitation since it can be
# met by rearranging the hypothesis order.
# (rl 2-Oct-2006) removed extraneous line found by Jason Orendorff
# (sf 27-Jan-2013) ported to Python 3, added support for compressed proofs
# and file inclusion

import sys
import itertools
import os.path
import argparse


class MMError(Exception):
    """Class of Metamath errors."""
    pass


class MMKeyError(MMError, KeyError):
    """Class of Metamath key errors."""
    pass


def vprint(vlevel, *args):
    """Print log message if verbosity level is higher than the argument."""
    if verbosity >= vlevel:
        print(*args, file=logfile)


class toks:
    """Class of sets of tokens from which functions read as in an input
    stream.
    """

    def __init__(self, lines):
        """Construct a toks with the given list of lines, an empty tokbuf
        list, and an empty set of names of imported files.
        """
        self.lines_buf = [lines]
        self.tokbuf = []
        self.imported_files = set()

    def read(self):
        """Read the next token."""
        while self.tokbuf == []:
            line = self.lines_buf[-1].readline()
            if not line:
                self.lines_buf.pop().close()
                if not self.lines_buf:
                    return None
            else:
                self.tokbuf = line.split()
                self.tokbuf.reverse()
        return self.tokbuf.pop()

    def readf(self):
        """Read the next token once included files have been expanded.  In the
        latter case, the name of the expanded file is added to a list so as to
        avoid multiple imports.
        """
        tok = self.read()
        while tok == '$[':
            filename = self.read()
            endbracket = self.read()
            if endbracket != '$]':
                raise MMError('Inclusion command not terminated')
            filename = os.path.realpath(filename)
            if filename not in self.imported_files:
                self.lines_buf.append(open(filename, 'r'))
                self.imported_files.add(filename)
            tok = self.read()
        return tok

    def readc(self):
        """Read the next token once included files have been expanded and
        ignoring comments.
        """
        while 1:
            tok = self.readf()
            if tok == '$(':
                while tok != '$)':
                    tok = self.read()
            else:
                return tok

    def readstat(self):
        """Read tokens from the input (assumed to be at the beginning of a
        statement) and return the list of tokens until the next end-statement
        token '$.'.
        """
        stat = []
        tok = self.readc()
        while tok != '$.':
            if tok is None:
                raise MMError('EOF before $.')
            stat.append(tok)
            tok = self.readc()
        return stat


class Frame:
    """Class of frames, keeping track of the environment."""

    def __init__(self):
        """Construct an empty frame."""
        self.c = set()
        self.v = set()
        self.d = set()
        self.f = []
        self.f_labels = {}
        self.e = []
        self.e_labels = {}


class FrameStack(list):
    """Class of frame stacks, which extends lists (considered and used as
    stacks).
    """

    def push(self):
        """Push an empty frame to the stack."""
        self.append(Frame())

    def add_c(self, tok):
        """Add a constant to the frame stack top.  Allow local definitions."""
        if self.lookup_c(tok):
            raise MMError('const already defined and active')
        if self.lookup_v(tok):
            raise MMError('const already defined as var and active')
        self[-1].c.add(tok)

    def add_v(self, tok):
        """Add a variable to the frame stack top.  Allow local definitions."""
        if self.lookup_v(tok):
            raise MMError('var already defined and active')
        if self.lookup_c(tok):
            raise MMError('var already defined as const and active')
        self[-1].v.add(tok)

    def add_f(self, var, kind, label):
        """Add a floating hypothesis (ordered pair (variable, kind)) to the
        frame stack top.
        """
        if not self.lookup_v(var):
            raise MMError('var in $f not defined: {0}'.format(var))
        if not self.lookup_c(kind):
            raise MMError('const in $f not defined {0}'.format(kind))
        frame = self[-1]
        # The following line forbids multiple $f-statements for a given var.
        # If that restriction is removed, then 'make_assertion' should be
        # changed accordingly with the comment there.
        if any(var in fr.f_labels.keys() for fr in self):
            raise MMError('var in $f already typed by an active $f-statement')
        frame.f.append((var, kind))
        frame.f_labels[var] = label

    def add_e(self, stat, label):
        """Add an essential hypothesis (token tuple) to the frame stack
        top.
        """
        frame = self[-1]
        frame.e.append(stat)
        frame.e_labels[tuple(stat)] = label

    def add_d(self, stat):
        """Add a disjoint variable condition (ordered pair of variables) to
        the frame stack top.
        """
        self[-1].d.update((min(x, y), max(x, y))
                          for x, y in itertools.product(stat, stat) if x != y)

    def lookup_c(self, tok):
        """Return whether the given token is an active constant."""
        return any(tok in fr.c for fr in self)

    def lookup_v(self, tok):
        """Return whether the given token is an active variable."""
        return any(tok in fr.v for fr in self)

    def lookup_d(self, x, y):
        """Return whether the given ordered pair of tokens belongs to an
        active disjoint variable statement.
        """
        return any((min(x, y), max(x, y)) in fr.d for fr in self)

    def lookup_f(self, var):
        """Return the label of the active floating hypothesis which types the
        given variable.
        """
        for frame in self:
            try:
                return frame.f_labels[var]
            except KeyError:
                pass
        raise MMKeyError(var)

    def lookup_e(self, stmt):
        """Return the label of the (earliest) active essential hypothesis with
        the given statement.
        """
        stmt_t = tuple(stmt)
        for frame in self:
            try:
                return frame.e_labels[stmt_t]
            except KeyError:
                pass
        raise MMKeyError(stmt_t)

    def make_assertion(self, stat):
        """Return a quadruple (disjoint variable conditions, floating
        hypotheses, essential hypotheses, conclusion) describing the given
        assertion.
        """
        e_hyps = [eh for fr in self for eh in fr.e]
        mand_vars = {tok for hyp in itertools.chain(e_hyps, [stat])
                     for tok in hyp if self.lookup_v(tok)}
        dvs = {(x, y) for fr in self for (x, y) in
               fr.d.intersection(itertools.product(mand_vars, mand_vars))}
        f_hyps = []
        # If one allows Metamath databases with multiple $f-statements for a
        # given var, then one should use "reversed" in the next two lines and
        # use 'appendleft' from 'collections.deque' to get the latest f_hyp
        # corresponding to the given var.
        # The current version of 'add_f' forbids such multiple $f-statements.
        for fr in self:
            for v, k in fr.f:
                if v in mand_vars:
                    f_hyps.append((k, v))
                    mand_vars.remove(v)
        vprint(18, 'make_assertion:', dvs, f_hyps, e_hyps, stat)
        return (dvs, f_hyps, e_hyps, stat)


def apply_subst(stat, subst):
    """Return the token list resulting from the given substitution
    (dictionary) applied to the given statement (token list).
    """
    result = []
    for tok in stat:
        if tok in subst:
            result += subst[tok]
        else:
            result.append(tok)
    vprint(20, 'apply_subst:', stat, subst, '=', result)
    return result


class MM:
    """Class of ("abstract syntax trees" describing) Metamath databases."""

    def __init__(self, begin_label, stop_label):
        """Construct an empty Metamath database."""
        self.fs = FrameStack()
        self.labels = {}
        self.begin_label = begin_label
        self.stop_label = stop_label

    def read(self, toks):
        """Read the given token list to update the database and verify its
        proofs.
        """
        self.fs.push()
        label = None
        tok = toks.readc()
        while tok not in (None, '$}'):
            if tok == '$c':
                for tok in toks.readstat():
                    self.fs.add_c(tok)
            elif tok == '$v':
                for tok in toks.readstat():
                    self.fs.add_v(tok)
            elif tok == '$f':
                stat = toks.readstat()
                if not label:
                    raise MMError('$f must have label')
                if len(stat) != 2:
                    raise MMError('$f must have length 2')
                vprint(15, label, '$f', stat[0], stat[1], '$.')
                self.fs.add_f(stat[1], stat[0], label)
                self.labels[label] = ('$f', [stat[0], stat[1]])
                label = None
            elif tok == '$e':
                if not label:
                    raise MMError('$e must have label')
                stat = toks.readstat()
                self.fs.add_e(stat, label)
                self.labels[label] = ('$e', stat)
                label = None
            elif tok == '$a':
                if not label:
                    raise MMError('$a must have label')
                if label == self.stop_label:
                    sys.exit(0)
                if label == self.begin_label:
                    self.begin_label = None
                self.labels[label] = ('$a',
                                      self.fs.make_assertion(toks.readstat()))
                label = None
            elif tok == '$p':
                if not label:
                    raise MMError('$p must have label')
                if label == self.stop_label:
                    sys.exit(0)
                if label == self.begin_label:
                    self.begin_label = None
                stat = toks.readstat()
                proof = None
                try:
                    i = stat.index('$=')
                    proof = stat[i + 1:]
                    stat = stat[:i]
                except ValueError:
                    raise MMError('$p must contain a proof after $=')
                dvs, f_hyps, e_hyps, conclusion = self.fs.make_assertion(stat)
                if not self.begin_label:
                    vprint(2, 'verifying:', label)
                    self.verify(f_hyps, e_hyps, conclusion, proof)
                self.labels[label] = ('$p', (dvs, f_hyps, e_hyps, conclusion))
                label = None
            elif tok == '$d':
                self.fs.add_d(toks.readstat())
            elif tok == '${':
                self.read(toks)
            elif tok[0] != '$':
                label = tok
            else:
                print('Unknown token:', tok)
            tok = toks.readc()
        self.fs.pop()

    def find_vars(self, stat):
        """Return the list of variables in the given statement."""
        vars = []
        for x in stat:
            if x not in vars and self.fs.lookup_v(x):
                vars.append(x)
        return vars

    def step(self, step, stack):
        """Carry out the given proof step (given the label to treat and the
        current proof stack).  This modifies the given stack in place.
        """
        steptyp, stepdat = step
        vprint(10, 'step', steptyp, stepdat)
        if steptyp in ('$e', '$f'):
            stack.append(stepdat)
        elif steptyp in ('$a', '$p'):
            dvs0, f_hyps0, e_hyps0, conclusion0 = stepdat
            vprint(12, stepdat)
            npop = len(f_hyps0) + len(e_hyps0)
            sp = len(stack) - npop
            if sp < 0:
                raise MMError('stack underflow')
            subst = {}
            for k, v in f_hyps0:
                entry = stack[sp]
                if entry[0] != k:
                    raise MMError(
                        ("stack entry {2!s} does not match floating " +
                             "hypothesis ({0}, {1})").format(entry, k, v))
                subst[v] = entry[1:]
                sp += 1
            vprint(15, 'subst:', subst)
            for h in e_hyps0:
                entry = stack[sp]
                subst_h = apply_subst(h, subst)
                if entry != subst_h:
                    raise MMError(("stack entry {0!s} does not match " +
                                   "essential hypothesis {1!s}")
                                      .format(entry, subst_h))
                sp += 1
            for x, y in dvs0:
                vprint(16, 'dist', x, y, subst[x], subst[y])
                x_vars = self.find_vars(subst[x])
                y_vars = self.find_vars(subst[y])
                vprint(16, 'V(x) =', x_vars)
                vprint(16, 'V(y) =', y_vars)
                for x, y in itertools.product(x_vars, y_vars):
                    if x == y or not self.fs.lookup_d(x, y):
                        raise MMError("Disjoint variable violation: " +
                                          "{0} , {1}".format(x, y))
            del stack[len(stack) - npop:]
            stack.append(apply_subst(conclusion0, subst))
        vprint(12, 'stack:', stack)

    def treat_normal_proof(self, proof):
        """Return the proof stack once the given normal proof has been
        processed.
        """
        stack = []
        for label in proof:
            self.step(self.labels[label], stack)
        return stack

    def treat_compressed_proof(self, f_hyps, e_hyps, proof):
        """Return the proof stack once the given compressed proof for an
        assertion with the given $f and $e-hypotheses has been processed.
        """
        f_labels = [self.fs.lookup_f(v) for _, v in f_hyps]
        e_labels = [self.fs.lookup_e(s) for s in e_hyps]
        labels = f_labels + e_labels  # labels of implicit hypotheses
        idx_bloc = proof.index(')')  # index of end of label bloc
        labels += proof[1:idx_bloc]  # labels which will be referenced later
        compressed_proof = ''.join(proof[idx_bloc + 1:])
        vprint(5, 'labels:', labels)
        vprint(5, 'proof:', compressed_proof)
        proof_ints = []  # integers referencing the labels in 'labels'
        cur_int = 0  #  counter for radix conversion
        for ch in compressed_proof:
            if ch == 'Z':
                proof_ints.append(-1)
            elif 'A' <= ch and ch <= 'T':
                proof_ints.append(20 * cur_int + ord(ch) - 65)  # ord('A') = 65
                cur_int = 0
            else:  # 'U' <= ch and ch <= 'Y'
                cur_int = 5 * cur_int + ord(ch) - 84  # ord('U') = 85
        vprint(5, 'proof_ints:', proof_ints)
        label_end = len(labels)
        saved_stmts = [] # statements saved for later reuse (marked with a 'Z')
        stack = []  # proof stack
        for pf_int in proof_ints:
            vprint(10, 'stack:', stack)
            if pf_int == -1:
                # this means we should save the current step for later
                saved_stmts.append(stack[-1])
            elif 0 <= pf_int and pf_int < label_end:
                # pf_int denotes an implicit hypothesis or a label in the label block
                self.step(self.labels[labels[pf_int]], stack)
            elif label_end <= pf_int:
                # pf_int denotes an earlier proof step marked with a 'Z'
                # A proof step that has already been proved can be treated as
                # a dv-free and hypothesis-free axiom.
                self.step(('$a', ([], [], [], saved_stmts[pf_int - label_end])), stack)
        return stack

    def verify(self, f_hyps, e_hyps, conclusion, proof):
        """Verify that the given proof (in normal or compressed format) is a
        correct proof of the given assertion.
        """
        # It would not be useful to also pass the list of dv conditions of the
        # assertion as an argument since other dv conditions corresponding to
        # dummy variables should be 'lookup_d'ed anyway.
        if proof[0] == '(':  # compressed format
            stack = self.treat_compressed_proof(f_hyps, e_hyps, proof)
        else:  # normal format
            stack = self.treat_normal_proof(proof)
        vprint(10, 'stack at end of proof:', stack)
        if len(stack) != 1:
            raise MMError("Stack has more than one entry at end of proof (top " +
                "entry: {0!s} ; proved assertion: {1!s}).".format(
                    stack[0],
                    conclusion))
        if stack[0] != conclusion:
            raise MMError("Stack entry {0!s} does not match proved " +
                          " assertion {1!s}".format(stack[0], conclusion))

    def dump(self):
        """Print the labels of the database."""
        print(self.labels)


if __name__ == '__main__':
    """Parse the arguments and verify the given Metamath database."""
    parser = argparse.ArgumentParser(description='Verify a Metamath database.')
    parser.add_argument(
        'database',
        nargs='?',
        type=argparse.FileType(
            'r',
            encoding='ascii'),
        default=sys.stdin,
        help='database (file) to verify (defaults to stdin)')
    parser.add_argument(
        '-l',
        '--logfile',
        dest='logfile',
        type=argparse.FileType(
            'w',
            encoding='ascii'),
        default=sys.stderr,
        help='file to output logs (defaults to stderr)')
    parser.add_argument(
        '-v',
        '--verbosity',
        dest='verbosity',
        default=0,
        type=int,
        help='verbosity level')
    parser.add_argument(
        '-b',
        '--begin-label',
        dest='begin_label',
        type=str,
        help='assertion label where to begin verifying (included if $p)')
    parser.add_argument(
        '-s',
        '--stop-label',
        dest='stop_label',
        type=str,
        help='assertion label where to stop verifying (not included)')
    args = parser.parse_args()
    verbosity = args.verbosity
    database = args.database
    logfile = args.logfile
    vprint(1, 'mmverify.py -- Proof verifier for the Metamath language')
    mm = MM(args.begin_label, args.stop_label)
    vprint(1, 'Reading source file "{0}"...'.format(database.name))
    mm.read(toks(database))
    vprint(1, 'No errors were found.')
    # mm.dump()
