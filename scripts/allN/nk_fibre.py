"""The fibre of the tropical prevariety of N_K with the cut generators over one point of mass weights.

N_K (docs/allN-lemmas-k.md section 6) is the normalised system of central configurations in the coordinates of
Albouy and Kaloshin: positions X_t, Y_t and P_tl with
    P_tl^2 (X_t - X_l)(Y_t - Y_l) = 1,   X_t = sum_l m_l P_tl^3 (X_t - X_l),   Y_t = sum_l m_l P_tl^3 (Y_t - Y_l).
Weights: xi_t = v(X_t), eta_t = v(Y_t), zeta_tl = v(X_t - X_l), omega_tl = v(Y_t - Y_l).  With an extra leaf O
(the origin) and zeta_tO = xi_t, omega_tO = eta_t, both zeta and omega are ultrametrics on the K + 1 leaves.
Values (minus the weights; the largest must be attained twice):
    cut generator of a set S of bodies, colour z:  sum_{t in S} m_t (row of t)
        = sum_{t in S} m_t X_t - sum over crossing pairs of m_t m_l P_tl^3 (X_t - X_l)
        values: -u_t - xi_t (t in S) and kappa^z_tl - u_t - u_l (t in S, l not in S), kappa^z = (zeta + 3 omega)/2;
    colour w: the same with eta and kappa^w = (3 zeta + omega)/2.
A one-body set gives the row; the set of all bodies gives the centre of mass sum_t m_t X_t = 0.
This is the stratum in which no position is 0.  With --zero-z t (--zero-w t) the body t is at the origin in that
colour: X_t = 0, so zeta_tl = xi_l, the leaf O is the sibling of t in the tree of zeta, the row of t has no
position term, and the torque terms with X_t are absent.

Torque generators (--torque).  Y_t (z-row of t) - X_t (w-row of t) = sum_l m_l P_tl^3 (X_l Y_t - X_t Y_l): the
positions cancel.  Summed with the weights m_t over a set S the pairs inside S cancel:
    sum over crossing pairs (t in S, l not in S) of m_t m_l P_tl^3 (X_l Y_t - X_t Y_l),
with the values 3 (zeta_tl + omega_tl)/2 - u_t - u_l - xi_l - eta_t and the same with xi_t, eta_l.

If N_K has infinitely many solutions at generic masses, its solution set over a field of Hahn series with
m_t = c_t T^(u_t) has positive dimension, so its tropicalisation over u has positive dimension, and so has the
fibre of this prevariety over u.  So a finite fibre over one generic u gives finiteness at generic masses.

For each pair of binary trees on the K + 1 leaves: the search of fixedu_enum.py.  At each solution the dimension
of its cell in the fibre is NV minus the rank of the equalities that hold (ties on top of each condition, equal
heights of a node and its parent).  Float LPs (HiGHS), no certificates.

Rays.  Only unbounded cells matter (a positive-dimensional tropical variety is unbounded).  The polyhedron P of a
leaf of the search (tree order, the chosen ties and their inequalities) contains the cells found there.  For each
leaf with a solution x the script looks for a direction sigma != 0, orthogonal to the rotation, in the recession
cone of P (the same rows with right-hand side 0), with LPs at up to twelve random objectives in a box (the
optima are extreme rays).  For each sigma found it tests whether x + s sigma stays in the prevariety for large
s: for every condition, among the terms of largest slope the largest value is attained twice.  Reported per
solution: ray = 0 (P is bounded modulo the rotation), 1 (P has rays, and every ray tested leaves the prevariety;
not conclusive), 2 (a ray that stays in the prevariety: an unbounded cell).

Far search (--far R).  The conclusive test.  In the gauge rot.x = 0 (rot = +1 on the heights of zeta, -1 on those
of omega) and for a fixed generic vector c, the search is restricted to c.x >= R and then to c.x <= -R.  An
unbounded cell has points with |c.x| as large as one likes.  So no solution for a large R means that the fibre is
bounded modulo the rotation, in |c.x| < R, and has no ray.

Search above a value of Psi (--far-psi R).  Psi(a, b) = (zeta_ab + omega_ab)/2 - u_a - u_b on a body pair and
Psi(t, O) = -xi_t - eta_t - u_t on a position.  For each of these edges e the search is restricted to
Psi(e) >= R, in the gauge rot.x = 0.  No solution means that the largest value of Psi is below R on the whole
fibre (docs/allN-direct-route.md, Theorem D4).  Each solution is listed with its largest Psi.

Usage: PY scripts/allN/nk_fibre.py K u_0,...,u_{K-1} [--torque] [--sym] [--procs P] [--maxfound N] [--out FILE]
                                   [--far R | --far-psi R] [--zero-z T] [--zero-w T]
"""
import argparse
import multiprocessing as mp
import os
import sys
import time
from collections import Counter
from itertools import combinations

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fixedu_enum as FE  # noqa: E402

INF = FE.INF
TOL = 1e-7
ABSTOL = None      # --abs-tol: an absolute tolerance of a tie, for mass weights of a large range


class NEnum(FE.Enum):
    def __init__(self, K, u, torque=False, zero_z=None, zero_w=None, far=None):
        self.K, self.mode, self.u = K, 'ncuts', [float(x) for x in u]
        self.far = far                             # None, or (R, sign): only solutions with sign * c.x >= R
        self.farc = np.array([__import__('random').Random(77 + i).uniform(0.5, 1.5) *
                              (1 if i % 3 else -1) for i in range(2 * K)])
        self.zero = {'z': zero_z, 'w': zero_w}     # the body whose position is 0 in that colour, or None
        self.trees = [FE.analyse(t) for t in FE.all_trees(range(K + 1))]      # leaf K is the origin
        self.nn = K
        self.NV = 2 * K
        self.pairs = list(combinations(range(K), 2))
        self.conds = []
        for col in 'zw':
            for mask in range(1, 2 ** K):
                S = [i for i in range(K) if mask >> i & 1]
                ps = [((a, b) if a < b else (b, a)) for a in S for b in range(K) if not mask >> b & 1]
                St = [t for t in S if t != self.zero[col]]          # a body at the origin has no position term
                items = [('k', col, p) for p in ps] + [('pos', col, t) for t in St]
                cs = [-self.u[p[0]] - self.u[p[1]] for p in ps] + [-self.u[t] for t in St]
                if len(items) >= 1:
                    self.conds.append((col, 'C%s%d' % (col, mask), items, np.array(cs)))
        if torque:
            for mask in range(1, 2 ** K - 1):
                S = [i for i in range(K) if mask >> i & 1]
                items, cs = [], []
                for t in S:
                    for l in range(K):
                        if not mask >> l & 1:
                            for a_, b_ in ((t, l), (l, t)):            # ('tq', a, b): the term P^3 X_b Y_a
                                if b_ != self.zero['z'] and a_ != self.zero['w']:
                                    items.append(('tq', a_, b_))
                                    cs.append(-self.u[t] - self.u[l])
                if items:
                    self.conds.append(('t', 'T%d' % mask, items, np.array(cs)))
        self.h = FE.highspy.Highs()
        self.h.setOptionValue('output_flag', False)
        self.h2 = FE.highspy.Highs()
        self.h2.setOptionValue('output_flag', False)
        self.nlp = self.nodd = self.nretry = 0
        self.oddlog = []
        self.stack = []
        self.rnd = __import__('random').Random(5)
        # the edges of Psi: body pairs, and (t, K) for the position of t (absent in a stratum with t at the origin)
        self.edges = list(self.pairs) + [(t, K) for t in range(K) if t not in (zero_z, zero_w)]

    def search(self, out, maxfound):
        """as in fixedu_enum.py; a solution is recorded with the ray verdict of its leaf."""
        x = self.solve()
        if x is None:
            return
        best = None
        for ci, (M, (col, nm, ps, cs)) in enumerate(zip(self.mats, self.conds)):
            v = M @ x + cs
            if len(v) < 2:
                best = (INF, ci)
                break
            top = np.partition(v, -2)[-2:]
            gap = top[1] - top[0]
            if gap > (ABSTOL if ABSTOL is not None else TOL * (1 + abs(top[1]))) and (best is None or gap > best[0]):
                best = (gap, ci)
        if best is None:
            out.append((x, self.ray(x, self.rnd)))
            return
        ci = best[1]
        M, cs = self.mats[ci], self.conds[ci][3]
        n = len(cs)
        for i, i2 in combinations(range(n), 2):
            if len(out) >= maxfound:
                return
            rows = []
            e = M[i] - M[i2]
            c = cs[i2] - cs[i]
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

    def setup(self, iz, iw):
        pz, lz = self.trees[iz]
        pw, lw = self.trees[iw]
        nn, K = self.nn, self.K
        self.par = (pz, pw)
        # a body at the origin: it must be the sibling of the leaf O in that tree (their node has the two leaves
        # t and O only, so no other body meets t or O at that node); the height of their node is then not a
        # parameter (it is set to the height of its parent plus 1)
        self.skip = False
        cherry = []
        for col, lca, off, par in (('z', lz, 0, pz), ('w', lw, nn, pw)):
            t = self.zero[col]
            if t is not None:
                n0 = lca[(t, K)]
                if any(lca[(min(l, t), max(l, t))] == n0 or lca[(l, K)] == n0
                       for l in range(K) if l != t) or n0 == 0:
                    self.skip = True
                cherry.append((off + n0, off + par[n0]))
        self.cherry = [c_ for c_ in cherry if c_[1] >= 0]
        self.stack = []
        self.kap = {}
        for col, (cz, cw) in (('z', (0.5, 1.5)), ('w', (1.5, 0.5))):
            for p in self.pairs:
                e = np.zeros(self.NV)
                e[lz[p]] += cz
                e[nn + lw[p]] += cw
                self.kap[col, p] = e

        def vec(item):
            if item[0] == 'k':
                return self.kap[item[1], item[2]]
            e = np.zeros(self.NV)
            if item[0] == 'tq':
                a, b = item[1], item[2]
                p = (a, b) if a < b else (b, a)
                e[lz[p]] += 1.5
                e[nn + lw[p]] += 1.5
                e[lz[(b, K)]] -= 1.0               # xi_b
                e[nn + lw[(a, K)]] -= 1.0          # eta_a
                return e
            t = item[2]
            if item[1] == 'z':
                e[lz[(t, K)]] = -1.0
            else:
                e[nn + lw[(t, K)]] = -1.0
            return e
        self.mats = [np.array([vec(it) for it in items]) for col, nm, items, cs in self.conds]
        h = self.h
        h.clearModel()
        for i in range(self.NV):
            h.addVar(-INF, INF)
        self.tree_rows = []
        for i in range(1, nn):
            for off, par in ((0, pz), (nn, pw)):
                h.addRow(0.0, INF, 2, np.array([off + i, off + par[i]], dtype=np.int32), np.array([1.0, -1.0]))
                e = np.zeros(self.NV)
                e[off + i] = 1.0
                e[off + par[i]] = -1.0
                self.tree_rows.append(e)
        self.nrows = 2 * (nn - 1)
        for i, pi in cherry:
            if pi >= 0 and not self.skip:
                h.addRow(1.0, 1.0, 2, np.array([i, pi], dtype=np.int32), np.array([1.0, -1.0]))
                self.nrows += 1
        if self.far is not None:                   # gauge of the rotation, and the half space far from the origin
            R, sign = self.far
            rot = np.array([1.0] * nn + [-1.0] * nn)
            h.addRow(0.0, 0.0, self.NV, np.arange(self.NV, dtype=np.int32), rot)
            if isinstance(sign, tuple):            # an edge e of Psi: only the points with Psi(e) >= R at which
                e, c = self.psi_row(sign, lz, lw)  # e has the largest Psi of all edges
                nz = np.nonzero(e)[0].astype(np.int32)
                h.addRow(R - c, INF, len(nz), nz, e[nz])
                for ed in self.edges:
                    if ed != sign:
                        e2, c2 = self.psi_row(ed, lz, lw)
                        d = e - e2
                        nz = np.nonzero(d)[0].astype(np.int32)
                        if len(nz):
                            h.addRow(c2 - c, INF, len(nz), nz, d[nz])
                        elif c2 - c > 1e-12:       # Psi(ed) > Psi(e) at every point of this pair of trees
                            h.addRow(1.0, 1.0, 0, np.array([], dtype=np.int32), np.array([]))
                        else:
                            h.addRow(-INF, INF, 0, np.array([], dtype=np.int32), np.array([]))
                        self.nrows += 1
            else:
                h.addRow(R, INF, self.NV, np.arange(self.NV, dtype=np.int32), sign * self.farc)
            self.nrows += 2
        if self.skip:                              # no solution on this pair of trees
            h.addRow(1.0, 1.0, 0, np.array([], dtype=np.int32), np.array([]))
            self.nrows += 1
        self.ncherry = len(cherry)

    def psi_row(self, edge, lz, lw):
        """Psi(edge) = e.x + c: (zeta + omega)/2 - u_a - u_b on a body pair, -xi_t - eta_t - u_t on (t, K)."""
        a, b = edge
        e = np.zeros(self.NV)
        if b == self.K:
            e[lz[(a, b)]] -= 1.0
            e[self.nn + lw[(a, b)]] -= 1.0
            return e, -self.u[a]
        e[lz[(a, b)]] += 0.5
        e[self.nn + lw[(a, b)]] += 0.5
        return e, -self.u[a] - self.u[b]

    def psi_max(self, iz, iw, x):
        lz, lw = self.trees[iz][1], self.trees[iw][1]
        return max(float(e @ x + c) for e, c in (self.psi_row(ed, lz, lw) for ed in self.edges))

    def push(self, rows):
        self.stack.append(rows)
        return FE.Enum.push(self, rows)

    def pop(self, n):
        if n:
            self.stack.pop()
        FE.Enum.pop(self, n)

    def ray(self, x, rnd):
        """0: no recession direction of the leaf polyhedron outside the rotation; 1: one found, it leaves the
        prevariety; 2: one found that stays in the prevariety."""
        h = self.h2
        h.clearModel()
        for i in range(self.NV):
            h.addVar(-1.0, 1.0)
        for e in self.tree_rows:
            nz = np.nonzero(e)[0].astype(np.int32)
            h.addRow(0.0, INF, len(nz), nz, e[nz])
        for i, pi in self.cherry:
            h.addRow(0.0, 0.0, 2, np.array([i, pi], dtype=np.int32), np.array([1.0, -1.0]))
        for rows in self.stack:
            for e, (lo, hi) in rows:
                nz = np.nonzero(e)[0].astype(np.int32)
                if len(nz):
                    h.addRow(0.0, 0.0 if lo == hi else INF, len(nz), nz, e[nz])
        rot = np.array([1.0] * self.nn + [-1.0] * self.nn)
        h.addRow(0.0, 0.0, self.NV, np.arange(self.NV, dtype=np.int32), rot)
        sigs = []
        for _ in range(6):
            c = np.array([rnd.uniform(-1, 1) for _ in range(self.NV)])
            for sg in (1.0, -1.0):
                for i in range(self.NV):
                    h.changeColCost(i, -sg * c[i])
                h.run()
                if h.getModelStatus() != FE.highspy.HighsModelStatus.kOptimal:
                    continue
                sig = np.array(h.getSolution().col_value)
                if np.abs(sig).max() > 1e-6 and not any(np.abs(sig - t).max() < 1e-7 for t in sigs):
                    sigs.append(sig)
            if not sigs:
                return 0                   # the first two objectives found nothing: no ray
        verdict = 1
        for sig in sigs:                   # the extreme rays found: does one stay in the prevariety?
            stays = True
            for M, (col, nm, items, cs) in zip(self.mats, self.conds):
                sl = M @ sig
                top = [i for i in range(len(sl)) if sl[i] > sl.max() - 1e-7]
                v = np.sort((M @ x + cs)[top])
                if len(top) < 2 or v[-1] - v[-2] > 1e-6 * (1 + abs(v).max()):
                    stays = False
                    break
            if stays:
                verdict = 2
                self.last_ray = sig
                break
        return verdict

    def dim(self, x):
        rows = []
        for M, (col, nm, items, cs) in zip(self.mats, self.conds):
            v = M @ x + cs
            mx = v.max()
            top = [i for i in range(len(v)) if v[i] > mx - 1e-6 * (1 + abs(mx))]
            rows += [M[i] - M[top[0]] for i in top[1:]]
        rows += [e for e in self.tree_rows if abs(e @ x) <= 1e-6 * (1 + abs(x).max())]
        r = np.linalg.matrix_rank(np.array(rows), tol=1e-9) if rows else 0
        return self.NV - r - self.ncherry

    def describe(self, iz, iw, xr):
        x, ray = xr
        pz, lz = self.trees[iz]
        pw, lw = self.trees[iw]
        nn, K = self.nn, self.K
        return {'trees': [iz, iw], 'dim': int(self.dim(x)), 'ray': int(ray), 'psi': round(self.psi_max(iz, iw, x), 5),
                'zeta': {'%d%d' % p: round(float(x[lz[p]]), 5) for p in self.pairs},
                'xi': [round(float(x[lz[(t, K)]]), 5) for t in range(K)],
                'omega': {'%d%d' % p: round(float(x[nn + lw[p]]), 5) for p in self.pairs},
                'eta': [round(float(x[nn + lw[(t, K)]]), 5) for t in range(K)]}


_E = None
_SYM = False


_FAR = None


_PSI = False


_DEADLINE = None


_SAMPLE = None


def _init(K, u, torque=False, sym=False, zero_z=None, zero_w=None, far=None, psi=False, deadline=None, sample=None):
    global _E, _SYM, _FAR, _PSI, _DEADLINE, _SAMPLE
    _DEADLINE = deadline
    _SAMPLE = sample
    _E = NEnum(K, u, torque, zero_z, zero_w)
    _SYM = sym
    _FAR = far
    _PSI = psi


def _task(arg):
    iz, maxfound = arg
    if _DEADLINE is not None and time.time() > _DEADLINE:      # the pool takes all tasks at once: stop here
        return iz, None, 0, 0
    out = []
    n0, o0 = _E.nlp, _E.nodd
    for iw in (_SAMPLE[iz] if _SAMPLE is not None else range(iz if _SYM else 0, len(_E.trees))):
        for sign in ((None,) if _FAR is None else _E.edges if _PSI else (1.0, -1.0)):
            _E.far = None if sign is None else (_FAR, sign)
            _E.setup(iz, iw)
            sols = []
            _E.search(sols, maxfound)
            out += [_E.describe(iz, iw, x) for x in sols]
    return iz, out, _E.nlp - n0, _E.nodd - o0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('K', type=int)
    ap.add_argument('u')
    ap.add_argument('--procs', type=int, default=4)
    ap.add_argument('--maxfound', type=int, default=200)
    ap.add_argument('--torque', action='store_true')
    ap.add_argument('--sym', action='store_true', help='only omega tree >= zeta tree (the exchange of the colours)')
    ap.add_argument('--out', help='JSON file: the distinct points with the dimensions of their cells')
    ap.add_argument('--far', type=float, default=None,
                    help='only the solutions with |c.x| >= FAR, for a fixed generic c, in the gauge rot.x = 0')
    ap.add_argument('--far-psi', type=float, default=None,
                    help='only the solutions with Psi(e) >= FAR_PSI for some edge e (a body pair or a position)')
    ap.add_argument('--zero-z', type=int, default=None, help='the stratum X_t = 0 for this body t')
    ap.add_argument('--zero-w', type=int, default=None, help='the stratum Y_t = 0 for this body t')
    ap.add_argument('--parts', help='JSON lines file, one line for each zeta tree that is done')
    ap.add_argument('--resume', action='store_true', help='skip the zeta trees recorded in --parts')
    ap.add_argument('--sample', type=int, default=None,
                    help='search a random sample of this many ordered pairs of trees (with --seed) and not all pairs')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--abs-tol', type=float, default=None,
                    help='two terms tie if they differ by at most this (default: 1e-7 relative to the larger term; '
                         'with heights of the order of 1e6 the relative test accepts false points)')
    ap.add_argument('--hours', type=float, default=None,
                    help='give out no new zeta tree after H hours (the run is then INCOMPLETE and writes no --out)')
    a = ap.parse_args()
    assert not (a.sym and (a.zero_z is not None or a.zero_w is not None)), 'a stratum is not symmetric'
    assert a.far is None or a.far_psi is None
    assert not (a.sample and a.sym), 'a sample is taken from the ordered pairs'
    global ABSTOL
    ABSTOL = a.abs_tol                             # set before the pool forks
    psi = a.far_psi is not None
    if psi:
        a.far = a.far_psi

    u = [float(x) for x in a.u.split(',')]
    assert len(u) == a.K
    t0 = time.time()
    nt = len(FE.all_trees(range(a.K + 1)))
    import json
    found, nlp, nodd, skip = [], 0, 0, set()
    if a.resume and a.parts:
        try:
            for line in open(a.parts):
                try:
                    r = json.loads(line)
                except ValueError:
                    continue                       # a line cut by a stop
                if r['iz'] not in skip:
                    skip.add(r['iz'])
                    found += r['found']
                    nlp += r['lps']
                    nodd += r['odd']
        except FileNotFoundError:
            pass
    sample = None
    if a.sample:                                   # the same sample for the same seed, so that --resume holds
        rnd = __import__('random').Random(a.seed)
        chosen = set()
        while len(chosen) < min(a.sample, nt * nt):
            chosen.add((rnd.randrange(nt), rnd.randrange(nt)))
        sample = {}
        for iz, iw in sorted(chosen):
            sample.setdefault(iz, []).append(iw)
    todo = [i for i in (range(nt) if sample is None else sorted(sample)) if i not in skip]
    deadline = None if a.hours is None else t0 + 3600 * a.hours

    fo = open(a.parts, 'a') if a.parts else None
    done = 0
    with mp.get_context('fork').Pool(a.procs, initializer=_init, initargs=(a.K, u, a.torque, a.sym, a.zero_z, a.zero_w, a.far, psi, deadline, sample)) as pool:
        for iz, out, n, o in pool.imap_unordered(_task, [(i, a.maxfound) for i in todo], chunksize=1):
            if out is None:
                continue
            found += out
            nlp += n
            nodd += o
            done += 1
            if fo:
                fo.write(json.dumps({'iz': iz, 'lps': n, 'odd': o, 'found': out}) + '\n')
                fo.flush()
            if done % 50 == 0:
                print('  zeta trees %d/%d, solutions %d, of dimension > 1: %d, leaves with a ray %d, rays that stay in '
                      'the prevariety %d, LPs %d, %.0fs'
                      % (done, len(todo), len(found), sum(d['dim'] > 1 for d in found), sum(d['ray'] > 0 for d in found),
                         sum(d['ray'] == 2 for d in found), nlp, time.time() - t0), flush=True)
    complete = done == len(todo)
    pts = {}
    for d in found:
        key = (tuple(sorted(d['zeta'].items())), tuple(d['xi']), tuple(sorted(d['omega'].items())), tuple(d['eta']))
        pts.setdefault(key, d)
    dims = Counter(d['dim'] for d in pts.values())
    rays = Counter(d['ray'] for d in found)
    print('nk_fibre K=%d%s u=%s: pairs of trees %d, zeta trees %d done before and %d now (%s), LPs %d, LPs with no verdict %d, '
          'solutions %d, distinct points %d, by dimension of the cell '
          '%s; leaves by ray verdict (0 none, 1 leaves the prevariety, 2 stays) %s; %.0fs' % (a.K, (' with torque generators' if a.torque else '') + ('' if a.far is None else (' Psi >= %g' if psi else ' far %g') % a.far) + ('' if a.zero_z is None else ' X_%d = 0' % a.zero_z) + ('' if a.zero_w is None else ' Y_%d = 0' % a.zero_w), a.u + ('' if sample is None else ' SAMPLE of %d ordered pairs of trees, seed %d,' % (sum(map(len, sample.values())), a.seed)), nt * nt, len(skip), done, 'COMPLETE' if complete else 'INCOMPLETE', nlp, nodd, len(found), len(pts), dict(sorted(dims.items())), dict(sorted(rays.items())), time.time() - t0))
    if a.out and complete:
        json.dump({'K': a.K, 'u': u, 'torque': a.torque, 'sym': a.sym, 'sample': a.sample, 'seed': a.seed, 'far': a.far, 'far_is_psi': psi, 'lps': nlp, 'lp_status_other': nodd,
                   'solutions': len(found), 'dims': dict(dims), 'rays': dict(rays), 'points': list(pts.values()),
                   'ray_leaves': [d for d in found if d['ray'] > 0][:2000]}, open(a.out, 'w'))
    if found:
        ps = sorted(d['psi'] for d in pts.values())
        print('   largest Psi at the distinct points: min %g, median %g, max %g' % (ps[0], ps[len(ps) // 2], ps[-1]))
    for d in [d for d in found if d['ray'] == 2][:6]:
        print('   RAY in the prevariety: xi %s  eta %s  zeta %s  omega %s' % (d['xi'], d['eta'], d['zeta'], d['omega']))
    for d in sorted(pts.values(), key=lambda d: (-d['dim'], d['trees']))[:12]:
        print('   dim %d  xi %s  eta %s  zeta %s  omega %s' % (d['dim'], d['xi'], d['eta'], d['zeta'], d['omega']))


if __name__ == '__main__':
    main()
