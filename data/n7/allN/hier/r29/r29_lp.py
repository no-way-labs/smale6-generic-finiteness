"""R29: search of the fibre over a mass vector u of the prevariety of the cut generators of N_n.

No lemma of the note is used in the search.  For a pair of binary trees (zeta on its leaves, omega on its
leaves; a child at least as high as its parent, so every pair of ultrametrics is covered) the unknowns are the
heights of the inner nodes.  The rotation is removed by: height of the zeta root = 0.
Conditions: for every nonempty set S of bodies and both colours, the largest term value over the edges
between S and its complement in the n + 1 vertices is attained twice.  Term values:
   colour z:  pair (a, b): zeta/2 + 3 omega/2 - u_a - u_b;   O-edge (t, O): -xi_t - u_t  (absent if X_t = 0)
   colour w:  pair (a, b): 3 zeta/2 + omega/2 - u_a - u_b;   O-edge (t, O): -eta_t - u_t (absent if Y_t = 0)
Strata: --zs s puts X_s = 0 (the zeta tree is a tree on the bodies and xi_t = zeta_ts for t != s);
        --ws r puts Y_r = 0.
Search in a pair of trees: solve the LP; take the first condition that fails at the LP point; branch on the
two terms that tie on top.  Float LPs (HiGHS), no certificates.

Modes:
  --mode list            one point for each leaf of the search; the statements of Theorem D4 are tested at it
  --mode far --R r       for each edge e: the same search with the extra row Psi(e) >= r
  --mode max             for each edge e: maximise Psi(e) subject to Psi(e) >= Psi(e') for all edges e' and
                         Psi(e) <= CAP, by branch and bound.  The largest result is the largest Psi* on the fibre.
  --sample N SEED        a random sample of N ordered pairs of trees
  --freescale            control: the rows lambda X_t = sum ..., lambda Y_t = sum ... with a free lambda (one more
                         unknown, the weight of lambda, in every O-edge).  This system has a continuum.
An LP that ends with a status other than optimal or infeasible is solved again from a cold start and then
without presolve; the ones that stay undecided are counted.
Usage: PY r29_lp.py N --u u0,..,u_{N-1} [--zs s] [--ws r] --mode list|far|max [--R r] [--procs 4]
                    [--sample N SEED] [--freescale]
"""
import argparse
import multiprocessing as mp
import os
import sys
import time
from itertools import combinations

import highspy
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r29_common as C  # noqa: E402

HINF = highspy.kHighsInf


class Fibre:
    def __init__(self, n, u, zs, ws, reltol=1e-7):
        self.n, self.u, self.zs, self.ws = n, [float(x) for x in u], zs, ws
        self.scale = 1.0 + max(self.u) - min(self.u)
        self.tol = reltol * self.scale
        self.cap = 1e4 * self.scale
        self.h = highspy.Highs()
        self.h.setOptionValue('output_flag', False)
        self.nlp = self.nodd = 0
        self.freescale = False      # control: a free scale factor lambda in the rows, lambda X_t = sum ...

    def idx(self, col, a, b):
        """index of the height variable of the edge (a, b), or None if the height is infinite"""
        n = self.n
        lca = self.lz if col == 'z' else self.lw
        s = self.zs if col == 'z' else self.ws
        off = 0 if col == 'z' else self.nz
        if b == n and s is not None:
            if a == s:
                return None
            return off + lca[C.pr(a, s)]
        return off + lca[(a, b)]

    def psi_vec(self, e):
        a, b = e
        iz, iw = self.idx('z', a, b), self.idx('w', a, b)
        if iz is None or iw is None:
            return None
        v = np.zeros(self.NV)
        if b == self.n:
            v[iz] -= 1.0
            v[iw] -= 1.0
            if self.freescale:
                v[self.NV - 1] -= 1.0
            return v, -self.u[a]
        v[iz] += 0.5
        v[iw] += 0.5
        return v, -self.u[a] - self.u[b]

    def term(self, e, col):
        a, b = e
        iz, iw = self.idx('z', a, b), self.idx('w', a, b)
        v = np.zeros(self.NV)
        if b == self.n:
            own = iz if col == 'z' else iw
            if own is None:
                return None
            v[own] -= 1.0
            if self.freescale:
                v[self.NV - 1] -= 1.0
            return v, -self.u[a]
        v[iz] += 0.5 if col == 'z' else 1.5
        v[iw] += 1.5 if col == 'z' else 0.5
        return v, -self.u[a] - self.u[b]

    def setup(self, tz, tw):
        n = self.n
        pz, self.lz = C.tree_struct(tz)
        pw, self.lw = C.tree_struct(tw)
        self.nz, self.nw = len(pz), len(pw)
        self.NV = self.nz + self.nw + (1 if self.freescale else 0)
        self.E = C.edges(n)
        self.psis = {e: self.psi_vec(e) for e in self.E}
        conds = []
        self.dead = False
        for S in C.subsets(n):
            cr = C.crossing(n, S)
            for col in 'zw':
                terms = [self.term(e, col) for e in cr]
                terms = [t for t in terms if t is not None]
                if len(terms) < 2:
                    self.dead = True
                conds.append(terms)
        self.M = [np.array([t[0] for t in terms]) for terms in conds]
        self.c = [np.array([t[1] for t in terms]) for terms in conds]
        h = self.h
        h.clearModel()
        for i in range(self.NV):
            h.addVar(-HINF, HINF)
        self.nrows = 0
        for i in range(1, self.nz):
            self.row({i: 1.0, pz[i]: -1.0}, 0.0, HINF)
        for i in range(1, self.nw):
            self.row({self.nz + i: 1.0, self.nz + pw[i]: -1.0}, 0.0, HINF)
        self.row({0: 1.0}, 0.0, 0.0)
        self.base_rows = self.nrows

    def row(self, d, lo, hi):
        items = [(i, v) for i, v in d.items() if v != 0.0]
        self.h.addRow(lo, hi, len(items), np.array([i for i, _ in items], dtype=np.int32),
                      np.array([v for _, v in items]))
        self.nrows += 1

    def push(self, rows):
        for e, lo, hi in rows:
            nzi = np.nonzero(e)[0].astype(np.int32)
            self.h.addRow(lo, hi, len(nzi), nzi, e[nzi])
        self.nrows += len(rows)
        return len(rows)

    def pop(self, k):
        if k:
            self.h.deleteRows(k, np.arange(self.nrows - k, self.nrows, dtype=np.int32))
            self.nrows -= k

    def set_objective(self, vec):
        for i in range(self.NV):
            self.h.changeColCost(i, float(vec[i]) if vec is not None else 0.0)
        self.h.changeObjectiveSense(highspy.ObjSense.kMaximize)

    def solve(self):
        self.nlp += 1
        self.h.run()
        st = self.h.getModelStatus()
        if st not in (highspy.HighsModelStatus.kOptimal, highspy.HighsModelStatus.kInfeasible):
            # solve again from a cold start, then without presolve
            self.h.clearSolver()
            self.h.run()
            st = self.h.getModelStatus()
            if st not in (highspy.HighsModelStatus.kOptimal, highspy.HighsModelStatus.kInfeasible):
                self.h.setOptionValue('presolve', 'off')
                self.h.clearSolver()
                self.h.run()
                st = self.h.getModelStatus()
                self.h.setOptionValue('presolve', 'choose')
        if st != highspy.HighsModelStatus.kOptimal:
            if st != highspy.HighsModelStatus.kInfeasible:
                self.nodd += 1
            return None
        return np.array(self.h.getSolution().col_value)

    def search(self, out, maxfound, obj=None):
        """obj = (vec, const, state): branch and bound for the largest value of vec.x + const; state['best']"""
        x = self.solve()
        if x is None:
            return
        if obj is not None:
            val = float(obj[0] @ x + obj[1])
            if val <= obj[2]['best'] + self.tol:
                return
        ci = None
        for j, (M, c) in enumerate(zip(self.M, self.c)):
            v = M @ x + c
            top = np.partition(v, -2)[-2:]
            if top[1] - top[0] > self.tol:
                ci = j
                break
        if ci is None:
            if obj is not None:
                obj[2]['best'] = val
                obj[2]['x'] = x
            else:
                out.append(x)
            return
        M, c = self.M[ci], self.c[ci]
        m = len(c)
        for i, i2 in combinations(range(m), 2):
            if obj is None and len(out) >= maxfound:
                return
            rows = []
            ok = True
            for k in range(m):
                if k == i:
                    continue
                e = M[i] - M[k]
                d = c[k] - c[i]
                eq = k == i2
                if not e.any():
                    if (eq and abs(d) > 1e-9 * self.scale) or (not eq and d > 1e-9 * self.scale):
                        ok = False
                        break
                else:
                    rows.append((e, d, d if eq else HINF))
            if not ok:
                continue
            nr = self.push(rows)
            self.search(out, maxfound, obj)
            self.pop(nr)

    def point(self, x):
        """the dicts Z, W over the edges of the n + 1 vertices"""
        Z, W = {}, {}
        for (a, b) in self.E:
            iz, iw = self.idx('z', a, b), self.idx('w', a, b)
            Z[(a, b)] = C.INF if iz is None else float(x[iz])
            W[(a, b)] = C.INF if iw is None else float(x[iw])
        return Z, W


_F = None
_TZ = _TW = None
_MODE = None
_R = None
_FREESCALE = False


def _init(n, u, zs, ws, mode, R):
    global _F, _TZ, _TW, _MODE, _R
    _F = Fibre(n, u, zs, ws)
    _F.freescale = _FREESCALE
    _TZ = C.all_binary_trees(range(n + 1) if zs is None else range(n))
    _TW = C.all_binary_trees(range(n + 1) if ws is None else range(n))
    _MODE, _R = mode, R


def _task(arg):
    iz, iws = arg if isinstance(arg, tuple) else (arg, None)
    F = _F
    n0, o0 = F.nlp, F.nodd
    res = []
    for iw in (range(len(_TW)) if iws is None else iws):
        F.setup(_TZ[iz], _TW[iw])
        if F.dead:
            continue
        if _MODE == 'list':
            F.set_objective(None)
            sols = []
            F.search(sols, 10 ** 9)
            for x in sols:
                res.append((iz, iw, None, None, F.point(x)))
        else:
            for e in F.E:
                pv = F.psis[e]
                if pv is None:
                    continue
                rows = []
                if _MODE == 'far':
                    F.set_objective(None)
                    rows.append((pv[0], _R - pv[1], HINF))
                else:
                    F.set_objective(pv[0])
                    rows.append((pv[0], -HINF, F.cap - pv[1]))
                    for e2 in F.E:
                        p2 = F.psis[e2]
                        if e2 == e or p2 is None:
                            continue
                        d = pv[0] - p2[0]
                        if d.any():
                            rows.append((d, p2[1] - pv[1], HINF))
                        elif p2[1] - pv[1] > 1e-9 * F.scale:
                            rows = None
                            break
                if rows is None:
                    continue
                nr = F.push(rows)
                if _MODE == 'far':
                    sols = []
                    F.search(sols, 1)
                    for x in sols:
                        res.append((iz, iw, e, None, F.point(x)))
                else:
                    state = {'best': -HINF, 'x': None}
                    F.search(None, 0, (pv[0], pv[1], state))
                    if state['x'] is not None:
                        res.append((iz, iw, e, state['best'], F.point(state['x'])))
                F.pop(nr)
    return res, F.nlp - n0, F.nodd - o0


def run(n, u, zs, ws, mode, R=None, procs=4, sample=None, freescale=False):
    """sample = (number of pairs of trees, seed): a random sample of the ordered pairs of trees"""
    global _FREESCALE
    _FREESCALE = freescale
    nz = len(C.all_binary_trees(range(n + 1) if zs is None else range(n)))
    nw = len(C.all_binary_trees(range(n + 1) if ws is None else range(n)))
    if sample is None:
        tasks = list(range(nz))
        npairs = nz * nw
    else:
        import random
        rnd = random.Random(sample[1])
        by = {}
        for _ in range(sample[0]):
            by.setdefault(rnd.randrange(nz), set()).add(rnd.randrange(nw))
        tasks = [(iz, sorted(s)) for iz, s in sorted(by.items())]
        npairs = sum(len(t[1]) for t in tasks)
    found, nlp, nodd = [], 0, 0
    if procs <= 1:
        _init(n, u, zs, ws, mode, R)
        for t in tasks:
            r, a, b = _task(t)
            found += r
            nlp += a
            nodd += b
    else:
        with mp.get_context('fork').Pool(procs, initializer=_init, initargs=(n, u, zs, ws, mode, R)) as pool:
            for r, a, b in pool.imap_unordered(_task, tasks, chunksize=1):
                found += r
                nlp += a
                nodd += b
    found.sort(key=lambda r: (r[0], r[1], str(r[2])))
    return found, nlp, nodd, npairs


def report(n, u, zs, ws, mode, R, found, nlp, nodd, npairs, secs, show=2):
    uf = [float(x) for x in u]
    scale = 1.0 + max(uf) - min(uf)
    tol = 1e-6 * scale
    head = 'r29_lp n = %d, u = %s, stratum %s, mode %s%s: %d pairs of trees; LPs %d; LPs neither optimal nor ' \
           'infeasible %d; %.0f s' % (n, ','.join(str(x) for x in u),
                                      'main' if zs is None and ws is None else
                                      ' '.join(([('X_%d = 0' % zs)] if zs is not None else []) +
                                               ([('Y_%d = 0' % ws)] if ws is not None else [])),
                                      mode, (' R = %s' % R) if mode == 'far' else '', npairs, nlp, nodd, secs)
    print(head)
    if not found:
        print('   points found: 0')
        sys.stdout.flush()
        return
    if _FREESCALE:
        bests = [b for _, _, _, b, _ in found if b is not None]
        print('   control with a free scale factor in the rows: %d results; largest value of Psi(e) = %g '
              '(the cap of the search is %g)' % (len(found), max(bests) if bests else float('nan'), 1e4 * scale))
        sys.stdout.flush()
        return
    stats = {'points': 0, 'cut condition fails': 0, 'not ultrametric': 0}
    fails = {}
    vals = {}
    ncyc = 0
    examples = []
    for iz, iw, e, best, (Z, W) in found:
        stats['points'] += 1
        if not (C.is_ultra(n, Z, tol) and C.is_ultra(n, W, tol)):
            stats['not ultrametric'] += 1
        if C.cut_failures(n, uf, Z, W, tol):
            stats['cut condition fails'] += 1
        a = C.analyse(n, uf, Z, W, tol)
        ncyc += len(a['cycles'])
        for f in a['fail']:
            fails[f] = fails.get(f, 0) + 1
        key = round(a['psistar'], 4)
        if key not in vals:
            vals[key] = a
            examples.append((key, Z, W, a))
    print('   points found: %d; not ultrametric %d; with a cut condition that fails (recomputed from the '
          'monomials) %d; simple cycles of B over all points %d' %
          (stats['points'], stats['not ultrametric'], stats['cut condition fails'], ncyc))
    print('   failures of the statements of Theorem D4: %s' % (fails if fails else 'none'))
    ks = sorted(vals)
    print('   distinct values of Psi* (%d): %s' % (len(ks), ', '.join('%g' % k for k in ks[:60])))
    print('   largest Psi* = %g; bound of Theorem D4 = %g' %
          (ks[-1], (2 * n - 1) * sum(abs(x) for x in uf) / 3))
    for key, Z, W, a in sorted(examples, key=lambda t: -t[0])[:show]:
        print('   example with Psi* = %g: E* = %s' % (key, a['Estar']))
        print('      zeta  = %s' % {'%d%s' % (p[0], 'O' if p[1] == n else p[1]): round(v, 4) for p, v in Z.items()})
        print('      omega = %s' % {'%d%s' % (p[0], 'O' if p[1] == n else p[1]): round(v, 4) for p, v in W.items()})
        for cy in a['cycles'][:3]:
            print('      cycle %s: N = %d, q = %s, N Psi* + q.u = %.2e' % (cy['edges'], cy['N'], cy['q'], cy['rel']))
    sys.stdout.flush()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('N', type=int)
    ap.add_argument('--u', required=True)
    ap.add_argument('--zs', type=int, default=None)
    ap.add_argument('--ws', type=int, default=None)
    ap.add_argument('--mode', choices=['list', 'far', 'max'], default='list')
    ap.add_argument('--R', type=float, default=None)
    ap.add_argument('--procs', type=int, default=4)
    ap.add_argument('--show', type=int, default=2)
    ap.add_argument('--sample', nargs=2, type=int, default=None, help='number of pairs of trees, seed')
    ap.add_argument('--freescale', action='store_true',
                    help='control: lambda X_t = sum ..., lambda Y_t = sum ... with a free lambda')
    a = ap.parse_args()
    u = [float(x) for x in a.u.split(',')]
    assert len(u) == a.N
    t0 = time.time()
    found, nlp, nodd, npairs = run(a.N, u, a.zs, a.ws, a.mode, a.R, a.procs, a.sample, a.freescale)
    if a.sample:
        print('(sample of the ordered pairs of trees, seed %d)' % a.sample[1])
    report(a.N, a.u.split(','), a.zs, a.ws, a.mode, a.R, found, nlp, nodd, npairs, time.time() - t0, a.show)


if __name__ == '__main__':
    main()
