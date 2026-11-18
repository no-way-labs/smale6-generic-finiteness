"""Exact check of a family of weight data at the mass weights u = (0, 1, 2, 3) (Remark 9.1 of the paper).

The member s = 1000 of the family was found by the session that read the release
(data/n7/allN/hier/r34/independent_small_data.log). With the vertex O written as 4, and with s for the
parameter that the paper calls chi, the family is

  zeta:  zeta_01 = zeta_12 = zeta_13 = zeta_1O = -s - 3,   zeta_02 = zeta_03 = 2s + 4,   zeta_23 = 2s + 6,
         zeta_0O = zeta_2O = zeta_3O = -s - 2;
  omega: omega_02 = omega_12 = omega_23 = omega_2O = 0,   omega_01 = omega_03 = omega_0O = 2,
         omega_13 = omega_1O = s + 5,   omega_3O = +infinity.

This program checks from Definition 3.3 of the paper alone, in exact arithmetic, that for every real s above
a bound S0 that it prints:

  - zeta and omega are ultrametrics on the four bodies and the vertex O (in every triangle the least of the
    three values is attained twice), with real values on the body pairs;
  - the cut condition holds for each of the 15 nonempty sets of bodies and both colours;
  - the largest value of Psi is s, and the edges {0,2}, {2,O}, {0,O}, {0,3} are the edges that attain it;
  - these four edges form a closed alternating sequence (Definition 5.1) with N = 0 and q = (1, 0, -3, 2)
    (Definition 6.1), and q . u = 0.

Method: every value is a polynomial a s + b of degree at most 1 with rational coefficients. Two values are
equal if they are equal as polynomials, and are otherwise compared by their values for large s; the program
records the number s at which the two polynomials cross. Above the largest such number, S0, every comparison
that the check made has the outcome that it used. The check is then repeated with numbers at s = 1000.

Controls: a changed height of zeta gives no ultrametric, a changed set of heights of omega gives an
ultrametric at which cut conditions fail, and q . u is not 0 at u = (0, 1, 30, 900), a vector of the chamber.

Usage: python3 scripts/allN/wd_u0123_check.py
"""
from fractions import Fraction
from functools import total_ordering
from itertools import combinations

n = 4
O = n                 # the vertex O
U = [0, 1, 2, 3]
CROSSINGS = []        # the numbers s at which two compared values cross


@total_ordering
class Aff:
    """The value a s + b, compared for large s."""

    def __init__(self, a, b=0):
        self.a, self.b = Fraction(a), Fraction(b)

    def __add__(self, o):
        o = o if isinstance(o, Aff) else Aff(0, o)
        return Aff(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __neg__(self):
        return Aff(-self.a, -self.b)

    def __sub__(self, o):
        return self + (-o if isinstance(o, Aff) else Aff(0, -o))

    def half(self):
        return Aff(self.a / 2, self.b / 2)

    def __eq__(self, o):
        o = o if isinstance(o, Aff) else Aff(0, o)
        if self.a != o.a and (self.a, self.b) != (o.a, o.b):
            CROSSINGS.append((o.b - self.b) / (self.a - o.a))
        return (self.a, self.b) == (o.a, o.b)

    def __lt__(self, o):
        o = o if isinstance(o, Aff) else Aff(0, o)
        if self.a != o.a:
            CROSSINGS.append((o.b - self.b) / (self.a - o.a))
        return (self.a, self.b) < (o.a, o.b)

    def __hash__(self):
        return hash((self.a, self.b))

    def at(self, s):
        return self.a * s + self.b

    def __repr__(self):
        return '%s s + %s' % (self.a, self.b)


INF = None            # the value +infinity
S = Aff(1, 0)


def family():
    zeta = {(0, 1): -S - 3, (1, 2): -S - 3, (1, 3): -S - 3, (1, 4): -S - 3,
            (0, 2): S + S + 4, (0, 3): S + S + 4, (2, 3): S + S + 6,
            (0, 4): -S - 2, (2, 4): -S - 2, (3, 4): -S - 2}
    omega = {(0, 2): Aff(0), (1, 2): Aff(0), (2, 3): Aff(0), (2, 4): Aff(0),
             (0, 1): Aff(0, 2), (0, 3): Aff(0, 2), (0, 4): Aff(0, 2),
             (1, 3): S + 5, (1, 4): S + 5, (3, 4): INF}
    return zeta, omega


def at(h, s):
    return {e: (INF if v is INF else v.at(s)) for e, v in h.items()}


def key(x, y):
    return (min(x, y), max(x, y))


def is_ultrametric(h):
    for a, b, c in combinations(range(n + 1), 3):
        fin = sorted(v for v in (h[key(a, b)], h[key(b, c)], h[key(a, c)]) if v is not INF)
        if len(fin) == 1:                     # two infinite values and a finite one
            return False
        if len(fin) >= 2 and fin[0] != fin[1]:
            return False
    return True


def psi(zeta, omega, e):
    a, b = e
    if b == O:
        if zeta[e] is INF or omega[e] is INF:
            return None                      # minus infinity
        return -zeta[e] - omega[e] - U[a]
    v = zeta[e] + omega[e]
    return (v.half() if isinstance(v, Aff) else Fraction(v) / 2) - U[a] - U[b]


def cut_terms(zeta, omega, body_set, colour):
    """The values Phi of the terms of the cut of a set of bodies in the given colour (Definition 3.3)."""
    own, other = (zeta, omega) if colour == 'z' else (omega, zeta)
    out = []
    for t in body_set:
        for l in range(n):
            if l not in body_set:
                e = key(t, l)
                out.append(psi(zeta, omega, e) + other[e])
        if own[(t, O)] is not INF:
            out.append(-own[(t, O)] - U[t])
    return out


def cut_failures(zeta, omega):
    bad = 0
    for r in range(1, n + 1):
        for body_set in combinations(range(n), r):
            for colour in 'zw':
                vals = sorted(cut_terms(zeta, omega, body_set, colour))
                if len(vals) < 2 or vals[-1] != vals[-2]:
                    bad += 1
    return bad


F = [(0, 2), (0, O)]      # f_0, f_1
G = [(2, O), (0, 3)]      # g_0, g_1


def check(zeta, omega):
    """Returns the largest Psi if (u, zeta, omega) is a weight datum with the sequence F, G as stated."""
    assert all(zeta[e] is not INF and omega[e] is not INF for e in zeta if e[1] != O)
    assert is_ultrametric(zeta) and is_ultrametric(omega)
    assert cut_failures(zeta, omega) == 0
    values = {e: psi(zeta, omega, e) for e in sorted(zeta)}
    top = max(v for v in values.values() if v is not None)
    estar = sorted(e for e in values if values[e] is not None and values[e] == top)
    assert estar == sorted(F + G)
    r = len(F)
    for i in range(r):
        assert omega[F[i]] is not INF and omega[F[i]] == omega[G[i]]      # f_i, g_i: equal heights in omega
        assert zeta[G[i]] == zeta[F[(i + 1) % r]]                          # g_i, f_{i+1}: equal heights in zeta
    return top


def n_and_q():
    """N and q of Definition 6.1: epsilon(f_i) = -1, epsilon(g_i) = +1."""
    N, q = 0, [0] * n
    for eps, es in ((-1, F), (1, G)):
        for a, b in es:
            if b == O:
                q[a] -= eps
            else:
                N += 3 * eps
                q[a] += 2 * eps
                q[b] += 2 * eps
    return N, q


def main():
    zeta, omega = family()
    top = check(zeta, omega)
    assert (top.a, top.b) == (1, 0)
    s0 = max(CROSSINGS)
    N, q = n_and_q()
    assert N == 0 and q == [1, 0, -3, 2] and sum(q[j] * U[j] for j in range(n)) == 0
    print('for every real s > %s: zeta and omega are ultrametrics, the 30 cut conditions hold, the largest Psi '
          'is s,' % s0)
    print('  and the edges that attain it are f = %s, g = %s (4 = O), a closed alternating sequence' % (F, G))
    print('  with N = %d, q = %s and q.u = 0' % (N, q))
    # the same check with numbers
    for s in (1000, int(s0) + 1):
        assert s > s0 and check(at(zeta, s), at(omega, s)) == s
    print('checked again with numbers at s = 1000 and s = %d' % (int(s0) + 1))
    # controls
    z2 = at(zeta, 1000)
    z2[(0, 2)] += 1
    assert not is_ultrametric(z2)
    w2 = at(omega, 1000)
    w2[(0, 1)] = w2[(0, 3)] = w2[(0, 4)] = 3
    assert is_ultrametric(w2) and cut_failures(at(zeta, 1000), w2) > 0
    print('controls: zeta_02 raised by 1 is no ultrametric; omega_01 = omega_03 = omega_0O = 3 is an '
          'ultrametric at which %d cut conditions fail' % cut_failures(at(zeta, 1000), w2))
    uc = [0, 1, 30, 900]
    print('q.u at u = (0, 1, 30, 900): %d' % sum(q[j] * uc[j] for j in range(n)))


if __name__ == '__main__':
    main()
