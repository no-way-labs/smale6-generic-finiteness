"""Cells of Ezw_K through one point of mass weights, by pairs of trees.

The mass weights u are fixed numbers.  A cell whose projection to the mass weights is not open misses a generic
u, so at a generic u this lists the cells with an open projection.

For each pair of rooted binary trees (one for zeta, one for omega) the unknowns are the heights of the internal
nodes (root height 0, a child at least as high as its parent; every ultrametric has such a tree).  The conditions:
  rows   every force row has two largest terms kappa^col_cl - u_l                      (the system Ezw_K)
  cuts   every cut (S, complement) has two largest crossing values kappa^col_ab - u_a - u_b
         (Ezw_K with the cut generators; a one-body set is a row)
  ccuts  the system C_K with centre 0 and its cut generators (docs/allN-hierarchical-emptiness.md section 9):
         colour z as in `cuts`; colour w for every nonempty set T without the centre, with the values
         kappa^w_ab - u_a - u_b of the crossing pairs and -u_a for a in T (the constant c = 1); the centre
         relation CR with the values -u_a - zeta_a0.  Here zeta_01 = 0 and the two roots are free.  No --sym.
Search inside a pair of trees: solve the LP; take the most violated condition at the LP point; branch on the pair
of terms that tie on top.  Float LPs (HiGHS), no certificates.  An LP whose status is neither optimal nor
infeasible is solved again from a cold start (without presolve, then by interior point); if it stays undecided
its branch is cut and the LP is counted.

Usage:
  fixedu_enum.py K rows|cuts|ccuts u_0,...,u_{K-1} [--procs P] [--first I --last J] [--out FILE] [--maxfound N]
                 [--sym] [--resume] [--hours H] [--trees I,J,...]
  (--first/--last: range of zeta trees; the trees are numbered in a fixed order; --trees: a list of zeta trees)
  --sym     only the pairs with omega tree >= zeta tree.  Exchanging zeta and omega exchanges the two colours and
            keeps u, so the pair (i, j) has a cell if and only if (j, i) has one (its mirror).
  --resume  skip the zeta trees already recorded in --out
  --hours   stop giving out new zeta trees after H hours (the run is then incomplete, and says so)
"""
import argparse
import json
import multiprocessing as mp
import sys
import time
from itertools import combinations

import highspy
import numpy as np

INF = highspy.kHighsInf
TOL = 1e-7


def all_trees(leaves):
    leaves = list(leaves)
    if len(leaves) == 1:
        return [leaves[0]]
    out = []
    first, rest = leaves[0], leaves[1:]
    for r in range(len(rest)):
        for comb in combinations(rest, r):
            left = [first] + list(comb)
            right = [x for x in rest if x not in comb]
            for lt in all_trees(left):
                for rt in all_trees(right):
                    out.append((lt, rt))
    return out


def analyse(tree):
    """(parent list of the internal nodes, node 0 = root; lca node of every pair)."""
    parent, lca = [], {}

    def rec(t, par):
        if not isinstance(t, tuple):
            return [t]
        idx = len(parent)
        parent.append(par)
        l = rec(t[0], idx)
        r = rec(t[1], idx)
        for a in l:
            for b in r:
                lca[(a, b) if a < b else (b, a)] = idx
        return l + r
    rec(tree, -1)
    return parent, lca


class Enum:
    def __init__(self, K, mode, u):
        self.K, self.mode, self.u = K, mode, [float(x) for x in u]
        self.trees = [analyse(t) for t in all_trees(range(K))]
        self.nn = K - 1                      # internal nodes of a binary tree
        self.NV = 2 * self.nn
        self.pairs = list(combinations(range(K), 2))
        self.conds = []      # (col, name, items, constants); an item is ('k', col, pair), ('zeta', pair) or None
        if mode == 'ccuts':
            for mask in range(1, 2 ** (K - 1)):                  # colour z: every cut once
                S = [i for i in range(K - 1) if mask >> i & 1]
                ps = [((a, b) if a < b else (b, a)) for a in S for b in range(K) if not (b < K - 1 and mask >> b & 1)]
                self.conds.append(('z', 'Cz%d' % mask, [('k', 'z', p) for p in ps],
                                   np.array([-self.u[p[0]] - self.u[p[1]] for p in ps])))
            for mask in range(1, 2 ** (K - 1)):                  # colour w: sets T of the bodies 1..K-1
                Tset = [i + 1 for i in range(K - 1) if mask >> i & 1]
                ps = [((a, b) if a < b else (b, a)) for a in Tset for b in range(K) if b not in Tset]
                items = [('k', 'w', p) for p in ps] + [None] * len(Tset)
                cs = [-self.u[p[0]] - self.u[p[1]] for p in ps] + [-self.u[a] for a in Tset]
                self.conds.append(('w', 'Cw%d' % mask, items, np.array(cs)))
            self.conds.append(('z', 'CR', [('zeta', (0, a)) for a in range(1, K)],
                               np.array([-self.u[a] for a in range(1, K)])))
        for col in ('zw' if mode != 'ccuts' else ''):
            if mode == 'rows':
                for c in range(K):
                    ps = [((c, l) if c < l else (l, c)) for l in range(K) if l != c]
                    cs = [-self.u[l] for l in range(K) if l != c]
                    self.conds.append((col, 'F%s%d' % (col, c), [('k', col, p) for p in ps], np.array(cs)))
            else:
                for mask in range(1, 2 ** (K - 1)):
                    S = [i for i in range(K - 1) if mask >> i & 1]
                    ps = [((a, b) if a < b else (b, a)) for a in S for b in range(K) if not (b < K - 1 and mask >> b & 1)]
                    cs = [-self.u[p[0]] - self.u[p[1]] for p in ps]
                    self.conds.append((col, 'C%s%d' % (col, mask), [('k', col, p) for p in ps], np.array(cs)))
        self.h = highspy.Highs()
        self.h.setOptionValue('output_flag', False)
        self.nlp = self.nodd = self.nretry = 0
        self.oddlog = []

    def setup(self, iz, iw):
        pz, lz = self.trees[iz]
        pw, lw = self.trees[iw]
        nn = self.nn
        self.kap = {}
        for col, (cz, cw) in (('z', (0.5, 1.5)), ('w', (1.5, 0.5))):
            for p in self.pairs:
                e = np.zeros(self.NV)
                e[lz[p]] += cz
                e[nn + lw[p]] += cw
                self.kap[col, p] = e
        zero = np.zeros(self.NV)

        def vec(item):
            if item is None:
                return zero
            if item[0] == 'k':
                return self.kap[item[1], item[2]]
            e = np.zeros(self.NV)                  # ('zeta', pair): minus the value of zeta on the pair
            e[lz[item[1]]] = -1.0
            return e
        self.mats = [np.array([vec(it) for it in items]) for col, nm, items, cs in self.conds]
        h = self.h
        h.clearModel()
        free = self.mode == 'ccuts'
        for i in range(self.NV):
            if free:
                h.addVar(-INF, INF)
            elif i == 0 or i == nn:
                h.addVar(0.0, 0.0)
            else:
                h.addVar(0.0, INF)
        for i in range(1, nn):
            h.addRow(0.0, INF, 2, np.array([i, pz[i]], dtype=np.int32), np.array([1.0, -1.0]))
            h.addRow(0.0, INF, 2, np.array([nn + i, nn + pw[i]], dtype=np.int32), np.array([1.0, -1.0]))
        self.nrows = 2 * (nn - 1)
        if free:                                   # the normalisation X_01 = 1: zeta_01 = 0
            h.addRow(0.0, 0.0, 1, np.array([lz[(0, 1)]], dtype=np.int32), np.array([1.0]))
            self.nrows += 1

    def push(self, rows):
        for e, lo in rows:
            nz = np.nonzero(e)[0].astype(np.int32)
            if len(nz) == 0:
                if lo > 1e-12:                 # an inconsistent constant condition: 0 >= lo > 0 or 0 = lo != 0
                    self.h.addRow(1.0, 1.0, 0, np.array([], dtype=np.int32), np.array([]))
                else:
                    self.h.addRow(-INF, INF, 0, np.array([], dtype=np.int32), np.array([]))
            else:
                self.h.addRow(lo[0], lo[1], len(nz), nz, e[nz])
        self.nrows += len(rows)
        return len(rows)

    def pop(self, n):
        if n:
            self.h.deleteRows(n, np.arange(self.nrows - n, self.nrows, dtype=np.int32))
            self.nrows -= n

    def solve(self):
        self.nlp += 1
        self.h.run()
        st = self.h.getModelStatus()
        decided = (highspy.HighsModelStatus.kOptimal, highspy.HighsModelStatus.kInfeasible)
        if st not in decided:                  # solve again from a cold start: without presolve, then interior point
            self.nretry += 1
            self.oddlog.append(str(st))
            for opts in ((('presolve', 'off'),), (('presolve', 'off'), ('solver', 'ipm'))):
                self.h.clearSolver()
                for k_, v in opts:
                    self.h.setOptionValue(k_, v)
                self.h.run()
                st = self.h.getModelStatus()
                if st in decided:
                    break
            self.h.setOptionValue('presolve', 'choose')
            self.h.setOptionValue('solver', 'choose')
            self.h.clearSolver()
            self.oddlog[-1] += ' -> ' + str(st)
        if st != highspy.HighsModelStatus.kOptimal:
            if st != highspy.HighsModelStatus.kInfeasible:
                self.nodd += 1                 # not decided: the branch is cut and counted
            return None
        return np.array(self.h.getSolution().col_value)

    def search(self, out, maxfound):
        x = self.solve()
        if x is None:
            return
        best = None
        for ci, (M, (col, nm, ps, cs)) in enumerate(zip(self.mats, self.conds)):
            v = M @ x + cs
            top = np.partition(v, -2)[-2:]
            gap = top[1] - top[0]
            if gap > TOL * (1 + abs(top[1])) and (best is None or gap > best[0]):
                best = (gap, ci)
        if best is None:
            out.append(x)
            return
        ci = best[1]
        M, cs = self.mats[ci], self.conds[ci][3]
        n = len(cs)
        for i, i2 in combinations(range(n), 2):
            if len(out) >= maxfound:
                return
            rows = []
            e = M[i] - M[i2]
            c = cs[i2] - cs[i]                 # M[i] x + cs[i] = M[i2] x + cs[i2]
            if not e.any():
                if abs(c) > 1e-9:
                    continue
            else:
                rows.append((e, (c, c)))
            ok = True
            for m in range(n):
                if m not in (i, i2):
                    e = M[i] - M[m]
                    c = cs[m] - cs[i]
                    if not e.any():
                        if c > 1e-9:
                            ok = False
                            break
                    else:
                        rows.append((e, (c, INF)))
            if not ok:
                continue
            k_ = self.push(rows)
            self.search(out, maxfound)
            self.pop(k_)

    def describe(self, iz, iw, x):
        pz, lz = self.trees[iz]
        pw, lw = self.trees[iw]
        nn = self.nn
        d = {'trees': [iz, iw], 'zeta': {'%d%d' % p: float(x[lz[p]]) for p in self.pairs},
             'omega': {'%d%d' % p: float(x[nn + lw[p]]) for p in self.pairs}, 'u': self.u}
        return d


_E = None
_SYM = False


def _init(K, mode, u, sym=False):
    global _E, _SYM
    _E = Enum(K, mode, u)
    _SYM = sym


def _task(arg):
    iz, maxfound = arg
    out = []
    n0, o0 = _E.nlp, _E.nodd
    _E.oddlog = []
    for iw in range(iz if _SYM else 0, len(_E.trees)):
        _E.setup(iz, iw)
        sols = []
        k0 = len(_E.oddlog)
        _E.search(sols, maxfound)
        for i in range(k0, len(_E.oddlog)):
            _E.oddlog[i] = 'omega tree %d: %s' % (iw, _E.oddlog[i])
        out += [_E.describe(iz, iw, x) for x in sols]
    return iz, out, _E.nlp - n0, _E.nodd - o0, list(_E.oddlog)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('K', type=int)
    ap.add_argument('mode', choices=['rows', 'cuts', 'ccuts'])
    ap.add_argument('u')
    ap.add_argument('--procs', type=int, default=4)
    ap.add_argument('--first', type=int, default=0)
    ap.add_argument('--last', type=int, default=None)
    ap.add_argument('--out')
    ap.add_argument('--maxfound', type=int, default=50, help='per pair of trees')
    ap.add_argument('--sym', action='store_true')
    ap.add_argument('--resume', action='store_true')
    ap.add_argument('--hours', type=float, default=None)
    ap.add_argument('--trees', help='comma list of zeta trees; replaces --first/--last')
    a = ap.parse_args()
    u = [float(x) for x in a.u.split(',')]
    assert len(u) == a.K
    assert not (a.sym and a.mode == 'ccuts'), 'the two colours of C_K are not exchanged by a symmetry'

    t0 = time.time()
    nt = len(all_trees(range(a.K)))
    last = nt if a.last is None else min(a.last, nt)
    found, nlp, nodd, nretry, done, skip = [], 0, 0, 0, 0, set()
    if a.resume and a.out:
        try:
            for line in open(a.out):
                try:
                    r = json.loads(line)
                except ValueError:
                    continue                   # a line cut by a stop
                skip.add(r['iz'])
                found += r['found']
                nlp += r['lps']
                nodd += r['odd']
        except FileNotFoundError:
            pass
    todo = [iz for iz in range(a.first, last) if iz not in skip]
    if a.trees:
        todo = [int(s) for s in a.trees.split(',') if int(s) not in skip]
    if a.sym:
        todo.sort()                            # with --sym the first zeta trees are the long tasks
    deadline = None if a.hours is None else t0 + 3600 * a.hours

    def gen():
        for iz in todo:
            if deadline is not None and time.time() > deadline:
                return
            yield (iz, a.maxfound)
    fo = open(a.out, 'a') if a.out else None
    with mp.get_context('fork').Pool(a.procs, initializer=_init, initargs=(a.K, a.mode, u, a.sym)) as pool:
        for iz, out, n, o, oddlog in pool.imap_unordered(_task, gen(), chunksize=1):
            found += out
            nlp += n
            nodd += o
            nretry += len(oddlog)
            done += 1
            if fo:
                rec = {'iz': iz, 'lps': n, 'odd': o, 'found': out}
                if oddlog:
                    rec['retried'] = oddlog
                fo.write(json.dumps(rec) + '\n')
                fo.flush()
            for s in oddlog:
                print('  zeta tree %d, %s' % (iz, s), flush=True)
            if done % 50 == 0:
                print('  zeta trees %d/%d, found %d, LPs %d, %.0fs' % (done, len(todo), len(found), nlp, time.time() - t0),
                      flush=True)
    complete = done == len(todo)
    print('fixedu K=%d %s u=%s: zeta trees %s of %d (%d done before, %d now, %s), omega trees %s; found %d; LPs %d; '
          'LPs solved again after a status neither optimal nor infeasible %d; LPs neither optimal nor infeasible %d; '
          '%.0fs'
          % (a.K, a.mode, a.u, a.trees if a.trees else '%d..%d' % (a.first, last), nt, len(skip), done,
             'COMPLETE' if complete else 'INCOMPLETE',
             'from the zeta tree on (--sym)' if a.sym else 'all', len(found), nlp, nretry, nodd, time.time() - t0))
    for d in found[:5]:
        print('   trees', d['trees'], 'zeta', {k_: round(v, 4) for k_, v in d['zeta'].items() if abs(v) > 1e-9},
              'omega', {k_: round(v, 4) for k_, v in d['omega'].items() if abs(v) > 1e-9})


if __name__ == '__main__':
    main()
