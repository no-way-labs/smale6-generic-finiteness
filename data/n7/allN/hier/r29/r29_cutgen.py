"""R29, check 1: the cut generators of N_n, expanded exactly from the rows, n = 2, ..., 5.

Polynomials are dicts {monomial: integer}, a monomial is a sorted tuple of (variable, exponent).
Variables: m_t, X_t, Y_t, P_tl (t < l).  The row of t in colour z is  X_t - sum_l m_l P_tl^3 (X_t - X_l).
Checks:
  (1) sum_{t in S} m_t row_t  =  sum_{t in S} m_t X_t - sum_{t in S, l not in S} m_t m_l P_tl^3 (X_t - X_l),
      as polynomials, for every nonempty set S of bodies, both colours;
  (2) the terms of the right side are one for each edge between S and its complement in the n + 1 vertices
      (bodies and O), and every partition of the n + 1 vertices into two nonempty sides occurs once;
  (3) at random weight points (two random ultrametrics on the n + 1 leaves, random u, exact rationals) the
      term of the edge e has the value Psi(e) + omega_e in colour z and Psi(e) + zeta_e in colour w,
      computed from the exponents of its monomial;
  (4) sum_t m_t Y_t row_t = sum_t m_t X_t Y_t - sum_{t<l} m_t m_l P_tl^3 (X_t - X_l)(Y_t - Y_l)  (I - U);
  (5) Y_t rowX_t - X_t rowY_t = sum_l m_l P_tl^3 (X_l Y_t - X_t Y_l)  (torque).
"""
import random
from fractions import Fraction as F
from itertools import combinations

import r29_common as C


def mono(*vs):
    d = {}
    for v in vs:
        d[v] = d.get(v, 0) + 1
    return tuple(sorted(d.items()))


def padd(p, q, s=1):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + s * v
        if r[k] == 0:
            del r[k]
    return r


def pmul(p, q):
    r = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            d = dict(k1)
            for a, e in k2:
                d[a] = d.get(a, 0) + e
            k = tuple(sorted(d.items()))
            r[k] = r.get(k, 0) + v1 * v2
            if r[k] == 0:
                del r[k]
    return r


def var(name):
    return {mono(name): 1}


def P3(t, l):
    a, b = C.pr(t, l)
    v = var(('P', a, b))
    return pmul(v, pmul(v, v))


def row(n, t, col):
    r = var((col, t))
    for l in range(n):
        if l != t:
            d = padd(var((col, t)), var((col, l)), -1)
            r = padd(r, pmul(var(('m', l)), pmul(P3(t, l), d)), -1)
    return r


def random_ultra(n, rnd):
    leaves = list(range(n + 1))
    rnd.shuffle(leaves)
    t = leaves[0]
    for x in leaves[1:]:
        opts = C._insert(t, x)
        t = opts[rnd.randrange(len(opts))]
    parent, lca = C.tree_struct(t)
    h = [F(0)] * len(parent)
    h[0] = F(rnd.randint(-20, 20), rnd.randint(1, 7))
    for i in range(1, len(parent)):
        h[i] = h[parent[i]] + F(rnd.randint(0, 30), rnd.randint(1, 7))     # 0 allowed: nodes may merge
    return {e: h[lca[e]] for e in C.edges(n)}


def main():
    rnd = random.Random(29)
    for n in (2, 3, 4, 5):
        nS = nterms = nval = 0
        parts = set()
        for S in C.subsets(n):
            for col in 'XY':
                lhs = {}
                for t in S:
                    lhs = padd(lhs, pmul(var(('m', t)), row(n, t, col)))
                rhs = {}
                terms = []
                for t in S:
                    rhs = padd(rhs, pmul(var(('m', t)), var((col, t))))
                    terms.append((t, n))
                    for l in range(n):
                        if l not in S:
                            d = padd(var((col, t)), var((col, l)), -1)
                            rhs = padd(rhs, pmul(pmul(var(('m', t)), var(('m', l))), pmul(P3(t, l), d)), -1)
                            terms.append(C.pr(t, l))
                assert lhs == rhs, (n, S, col)
                assert sorted(terms) == sorted(C.crossing(n, S)), (n, S)
                nS += 1
                nterms += len(terms)
            parts.add(frozenset([S, frozenset(range(n + 1)) - S]))
        assert len(parts) == 2 ** n - 1
        # values at random weight points
        for _ in range(200):
            Z, W = random_ultra(n, rnd), random_ultra(n, rnd)
            u = [F(rnd.randint(-30, 30), rnd.randint(1, 5)) for _ in range(n)]
            for S in C.subsets(n):
                for col in 'zw':
                    own, other = (Z, W) if col == 'z' else (W, Z)
                    for e in C.crossing(n, S):
                        a, b = e
                        if b == n:
                            val = u[a] + own[e]                       # m_t X_t
                        else:
                            val = u[a] + u[b] - 3 * (Z[e] + W[e]) / 2 + own[e]   # m_a m_b P^3 X_ab
                        assert -val == C.psi(n, u, Z, W, e) + other[e]
                        assert -val == C.term_value(n, u, Z, W, e, col)
                        nval += 1
        # I - U and the torque
        lhs = {}
        for t in range(n):
            lhs = padd(lhs, pmul(pmul(var(('m', t)), var(('Y', t))), row(n, t, 'X')))
        rhs = {}
        for t in range(n):
            rhs = padd(rhs, pmul(var(('m', t)), pmul(var(('X', t)), var(('Y', t)))))
        for t, l in combinations(range(n), 2):
            dx = padd(var(('X', t)), var(('X', l)), -1)
            dy = padd(var(('Y', t)), var(('Y', l)), -1)
            rhs = padd(rhs, pmul(pmul(var(('m', t)), var(('m', l))), pmul(P3(t, l), pmul(dx, dy))), -1)
        assert lhs == rhs
        for t in range(n):
            lhs = padd(pmul(var(('Y', t)), row(n, t, 'X')), pmul(var(('X', t)), row(n, t, 'Y')), -1)
            rhs = {}
            for l in range(n):
                if l != t:
                    d = padd(pmul(var(('X', l)), var(('Y', t))), pmul(var(('X', t)), var(('Y', l))), -1)
                    rhs = padd(rhs, pmul(var(('m', l)), pmul(P3(t, l), d)))
            assert lhs == rhs
        print('n = %d: %d cut generators (both colours) equal to the edge form, %d terms, %d partitions of the '
              '%d vertices, each once; %d term values equal to Psi + omega (z) or Psi + zeta (w) at 200 random '
              'points; I - U and the %d torque identities hold' % (n, nS, nterms, len(parts), n + 1, nval, n))


if __name__ == '__main__':
    main()
