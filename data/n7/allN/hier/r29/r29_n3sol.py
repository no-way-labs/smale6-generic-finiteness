"""R29, check 2: all solutions of N_3 modulo the rotation at numerically hierarchical masses, and the
valuations of their coordinates.

Masses m_t = c_t eps^{u_t}, eps = 10^-E.  The "valuation" of a number x is -log10|x| / E; the error is
|log10 of the leading coefficient| / E, so E is large (default 200) and the arithmetic is mpmath at
enough digits.

Solutions of N_3 (derivation in the report, section 2):
  - type L: all P_tl^3 = 1/M, M = m_0 + m_1 + m_2.  P_tl = M^(-1/3) rho^j, 27 choices, d_tl = P_tl^-2.
    With X_01 = 1: Y_01 = d_01, X_12 = x a root of d_01 x^2 + (d_01 + d_12 - d_02) x + d_12 = 0,
    Y_12 = d_12 / x.  54 solutions.
  - type C (X_l Y_t = X_t Y_l for all t, l): after the rotation X_t = Y_t = x_t, P_tl = s_tl / (x_t - x_l),
    s_tl = +-1 (t < l), s_01 = 1 modulo the rotation by -1.  With p = x_0 - x_1, q = x_1 - x_2 = tau p:
    a quintic for tau and p^3 = A(tau).  4 * 5 * 3 = 60 solutions.
Every solution is checked in the nine equations of N_3.  Then the valuations are rounded to multiples of 1/6
and the statements of Theorem D4 are tested with r29_common.analyse.
Usage: PY r29_n3sol.py PYLIB [--u 0,1,20] [--c 2,3,5] [--E 200]
"""
import argparse
import sys
from itertools import product

ap = argparse.ArgumentParser()
ap.add_argument('pylib')
ap.add_argument('--u', default='0,1,20')
ap.add_argument('--c', default='2,3,5')
ap.add_argument('--E', type=int, default=200)
ap.add_argument('--den', type=int, default=6)
args = ap.parse_args()
sys.set_int_max_str_digits(0)
sys.path.insert(0, args.pylib)
import mpmath as mpm  # noqa: E402
from mpmath import mp, mpf, mpc  # noqa: E402

import r29_common as C  # noqa: E402

u = [float(x) for x in args.u.split(',')]
cc = [mpf(x) for x in args.c.split(',')]
E = args.E
mp.dps = int(3 * E * (max(u) - min(u)) + 200)
m = [cc[t] * mpf(10) ** (-E * mpf(args.u.split(',')[t])) for t in range(3)]
M = m[0] + m[1] + m[2]
rho = mpm.exp(2j * mpm.pi / 3)


def val(x):
    return float(-mpm.log10(abs(x)) / E)


def residual(X, Y, P):
    """largest relative residual of the nine equations"""
    worst = mpf(0)
    for (t, l) in [(0, 1), (0, 2), (1, 2)]:
        worst = max(worst, abs(P[(t, l)] ** 2 * (X[t] - X[l]) * (Y[t] - Y[l]) - 1))
    for Q in (X, Y):
        for t in range(3):
            terms = [m[l] * P[C.pr(t, l)] ** 3 * (Q[t] - Q[l]) for l in range(3) if l != t]
            size = max([abs(Q[t])] + [abs(x) for x in terms])
            worst = max(worst, abs(Q[t] - sum(terms)) / size)
    return worst


sols = []
# ---- type L
k0 = mpm.root(M, 3) ** -1
for j in product(range(3), repeat=3):
    P = {(0, 1): k0 * rho ** j[0], (0, 2): k0 * rho ** j[1], (1, 2): k0 * rho ** j[2]}
    d = {e: 1 / P[e] ** 2 for e in P}
    a, b, c = d[(0, 1)], d[(0, 1)] + d[(1, 2)] - d[(0, 2)], d[(1, 2)]
    disc = mpm.sqrt(b * b - 4 * a * c)
    for sg in (1, -1):
        x = (-b + sg * disc) / (2 * a)
        X01, X12, X02 = mpc(1), x, 1 + x
        Y01, Y12 = d[(0, 1)], d[(1, 2)] / x
        Y02 = Y01 + Y12
        X0 = (m[1] * X01 + m[2] * X02) / M
        Y0 = (m[1] * Y01 + m[2] * Y02) / M
        X = [X0, X0 - X01, X0 - X02]
        Y = [Y0, Y0 - Y01, Y0 - Y02]
        sols.append(('L', j, sg, X, Y, P))
# ---- type C
for s02, s12 in product((1, -1), repeat=2):
    s01 = 1
    # polynomials in tau as coefficient lists, lowest degree first
    def pm(p, q):
        r = [mpf(0)] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for k, b in enumerate(q):
                r[i + k] += a * b
        return r

    def pa(p, q, s=1):
        r = [mpf(0)] * max(len(p), len(q))
        for i, a in enumerate(p):
            r[i] += a
        for i, b in enumerate(q):
            r[i] += s * b
        return r
    t1 = [mpf(0), mpf(1)]
    t2 = pm(t1, t1)
    o2 = pm([mpf(1), mpf(1)], [mpf(1), mpf(1)])
    t2o2 = pm(t2, o2)
    # tau^2 (1 + tau)^2 A = (m0 + m1) s01 tau^2 (1 + tau)^2 + m2 s02 tau^2 - m2 s12 (1 + tau)^2
    A = pa(pa([(m[0] + m[1]) * s01 * x for x in t2o2], [m[2] * s02 * x for x in t2]), [m[2] * s12 * x for x in o2], -1)
    # tau^2 (1 + tau)^2 B = (m1 + m2) s12 (1 + tau)^2 - m0 s01 tau^2 (1 + tau)^2 + m0 s02 tau^2
    B = pa(pa([(m[1] + m[2]) * s12 * x for x in o2], [m[0] * s01 * x for x in t2o2], -1), [m[0] * s02 * x for x in t2])
    quint = pa(pm(t1, A), B, -1)
    assert len(quint) == 6
    roots = mpm.polyroots(quint[::-1], maxsteps=2000, extraprec=4 * mp.dps)
    for ir, tau in enumerate(roots):
        Aval = (m[0] + m[1]) * s01 + m[2] * s02 / (1 + tau) ** 2 - m[2] * s12 / tau ** 2
        p0 = mpm.root(Aval, 3)
        for kk in range(3):
            p = p0 * rho ** kk
            q = tau * p
            x0 = m[1] * s01 / p ** 2 + m[2] * s02 / (p + q) ** 2
            X = [x0, x0 - p, x0 - p - q]
            P = {(0, 1): s01 / p, (0, 2): s02 / (p + q), (1, 2): s12 / q}
            sols.append(('C', (s01, s02, s12), (ir, kk), X, list(X), P))

print('r29_n3sol: masses c = %s, u = %s, eps = 1e-%d, %d digits; %d solutions (54 of type L, 60 of type C)'
      % (args.c, args.u, E, mp.dps, len(sols)))
worst = max(residual(X, Y, P) for _, _, _, X, Y, P in sols)
print('   largest relative residual of the nine equations over all solutions: %s' % mpm.nstr(worst, 3))
n = 3
den = args.den
maxdev = 0.0
stats = {}
vals = {}
dist = {}
tol = 1e-9
for typ, lab, lab2, X, Y, P in sols:
    Z, W = {}, {}
    dev = 0.0
    for (a, b) in C.edges(n):
        zx = X[a] if b == n else X[a] - X[b]
        wy = Y[a] if b == n else Y[a] - Y[b]
        for D, x in ((Z, zx), (W, wy)):
            v = val(x)
            r = round(v * den) / den
            dev = max(dev, abs(v - r))
            D[(a, b)] = r
    # P against the distances
    for e in P:
        dev = max(dev, abs(val(P[e]) + (Z[e] + W[e]) / 2))
    maxdev = max(maxdev, dev)
    ok_u = C.is_ultra(n, Z, tol) and C.is_ultra(n, W, tol)
    cf = C.cut_failures(n, u, Z, W, tol)
    a = C.analyse(n, u, Z, W, tol)
    key = (typ, round(a['psistar'], 4), tuple(a['Estar']),
           tuple(sorted((cy['N'], tuple(cy['q'])) for cy in a['cycles'])))
    stats[key] = stats.get(key, 0) + 1
    dk = (typ,) + tuple(round(Z[e] + W[e], 3) for e in C.edges(n))
    dist[dk] = dist.get(dk, 0) + 1
    for f in a['fail'] + (['not ultrametric'] if not ok_u else []) + (['a cut condition fails'] if cf else []):
        vals[f] = vals.get(f, 0) + 1
print('   valuations rounded to multiples of 1/%d; largest distance to the rounded value: %.4f' % (den, maxdev))
print('   failures (ultrametric, cut conditions recomputed from the monomials, statements of Theorem D4): %s'
      % (vals if vals else 'none'))
print('   type, Psi*, E*, (N, q) of the simple cycles of B: number of solutions')
for key in sorted(stats, key=str):
    print('      %s  Psi* = %g  E* = %s  cycles %s: %d' % (key[0], key[1], list(key[2]), list(key[3]), stats[key]))
print('   type, zeta + omega on the edges 01, 02, 0O, 12, 1O, 2O: number of solutions')
for dk in sorted(dist, key=str):
    print('      %s  %s: %d' % (dk[0], ', '.join('%g' % x for x in dk[1:]), dist[dk]))
