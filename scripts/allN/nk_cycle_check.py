"""The cycle relation of the top edges of Psi at recorded points of the fibre of N_K (docs/allN-direct-route.md).

Input: JSON files written by nk_fibre.py --out (plain or .gz).  For each recorded point:
  Psi(a, b) = (zeta_ab + omega_ab)/2 - u_a - u_b on a body pair, Psi(t, O) = -xi_t - eta_t - u_t on a position;
  E* = the edges with the largest Psi; B = the bipartite graph on the nodes of the two trees (on the K bodies and
  the origin O; nodes joined by an edge of length 0 are one node) with one edge for each e in E*, between the
  zeta-node and the omega-node of e.
Checked:
  (1) every vertex of B that meets an edge has degree at least 2 (Lemma 19 with the origin);
  (2) for every cycle of a basis of the cycle space of B, with the sign +1 on its edges in one direction and -1 in
      the other, N Psi* + q.u = 0, where N = sum of sign * (2 on a pair, -1 on a position) and
      q = sum of sign * (2 (1_a + 1_b) on a pair, -1_t on a position);
  (3) whether some cycle has N != 0.  Then Psi* = -q.u / N is fixed by the mass weights.
Float data (five decimals in the files); the tolerance of a tie is absolute (--tol, default 1e-3).

Usage: PY scripts/allN/nk_cycle_check.py FILE [FILE ...]
"""
import gzip
import json
import os
import sys
from collections import Counter
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fixedu_enum as FE  # noqa: E402


def load(fn):
    return json.load(gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn))


def merged_nodes(parent, lca, height, tol):
    """node -> representative, after joining a node with its parent when the heights agree."""
    rep = list(range(len(parent)))
    for i in range(1, len(parent)):                # parents come before children in `analyse`
        if abs(height[i] - height[parent[i]]) <= tol:
            rep[i] = rep[parent[i]]
    return rep


TOL = 1e-3      # absolute: two heights or two values of Psi closer than this are equal (the files have 5 decimals)


def check_point(K, u, trees, d, stats):
    (pz, lz), (pw, lw) = trees[d['trees'][0]], trees[d['trees'][1]]
    edges = [(a, b) for a in range(K) for b in range(a + 1, K)] + [(t, K) for t in range(K)]
    z = {e: (d['zeta']['%d%d' % e] if e[1] < K else d['xi'][e[0]]) for e in edges}
    w = {e: (d['omega']['%d%d' % e] if e[1] < K else d['eta'][e[0]]) for e in edges}
    tol = TOL
    psi = {e: ((z[e] + w[e]) / 2 - u[e[0]] - u[e[1]]) if e[1] < K else (-z[e] - w[e] - u[e[0]]) for e in edges}
    top = max(psi.values())
    estar = [e for e in edges if psi[e] > top - tol]
    hz, hw = {}, {}
    for e in edges:
        hz[lz[e]] = z[e]
        hw[lw[e]] = w[e]
    rz = merged_nodes(pz, lz, hz, tol)
    rw = merged_nodes(pw, lw, hw, tol)
    node = {e: (('z', rz[lz[e]]), ('w', rw[lw[e]])) for e in estar}
    deg = Counter(v for e in estar for v in node[e])
    stats['points'] += 1
    stats['estar_sizes'][len(estar)] += 1
    kinds = (any(e[1] == K for e in estar), any(e[1] < K for e in estar))
    stats['estar_kinds'][('position ' if kinds[0] else '') + ('pair' if kinds[1] else '')] += 1
    if min(deg.values()) < 2:
        stats['degree_fail'] += 1
        return
    # a basis of the cycle space: spanning forest by union-find, one cycle for each edge outside it
    par = {}
    adj = {}

    def find(x):
        while par.get(x, x) != x:
            x = par[x]
        return x
    cycles = []
    for e in estar:
        a, b = node[e]
        ra, rb = find(a), find(b)
        if ra != rb:
            par[ra] = rb
            adj.setdefault(a, []).append((b, e))
            adj.setdefault(b, []).append((a, e))
        else:                                      # the path from b to a in the forest, then e
            stack, seen = [(b, [])], {b}
            path = None
            while stack:
                x, p = stack.pop()
                if x == a:
                    path = p
                    break
                for y, f in adj.get(x, []):
                    if y not in seen:
                        seen.add(y)
                        stack.append((y, p + [f]))
            cycles.append(path + [e])
    found_n = False
    for cyc in cycles:
        N, q = 0, [0] * K
        for i, e in enumerate(cyc):                # B is bipartite: the edges of a closed walk alternate in direction
            s = 1 if i % 2 == 0 else -1
            if e[1] < K:
                N += 2 * s
                q[e[0]] += 2 * s
                q[e[1]] += 2 * s
            else:
                N -= s
                q[e[0]] -= s
        assert len(cyc) % 2 == 0
        res = N * top + sum(q[t] * u[t] for t in range(K))
        stats['worst'] = max(stats['worst'], abs(res))
        if abs(res) > 20 * tol * (1 + len(cyc)):
            stats['relation_fail'] += 1
        if N != 0:
            found_n = True
            stats['psi_values'][str(Fraction(-sum(Fraction(q[t]) * Fraction(u[t]).limit_denominator(10 ** 6)
                                                  for t in range(K)), N))] += 1
        elif any(q):
            stats['mass_relation_cycles'] += 1
        else:
            stats['balanced_cycles'] += 1
    stats['cycles'] += len(cycles)
    stats['with_N' if found_n else 'without_N'] += 1
    if not found_n:
        stats['no_N_examples'].append((d['trees'], round(top, 4), sorted(estar)))


def main():
    global TOL
    args = sys.argv[1:]
    if '--tol' in args:
        i = args.index('--tol')
        TOL = float(args[i + 1])
        del args[i:i + 2]
    for fn in args:
        dat = load(fn)
        K, u = dat['K'], dat['u']
        trees = [FE.analyse(t) for t in FE.all_trees(range(K + 1))]
        stats = {'points': 0, 'degree_fail': 0, 'relation_fail': 0, 'worst': 0.0, 'cycles': 0, 'with_N': 0,
                 'without_N': 0, 'mass_relation_cycles': 0, 'balanced_cycles': 0, 'estar_sizes': Counter(),
                 'estar_kinds': Counter(), 'psi_values': Counter(), 'no_N_examples': []}
        for d in dat['points']:
            check_point(K, u, trees, d, stats)
        print('%s: K=%d u=%s' % (fn, K, u))
        print('  points %d; a vertex of B of degree 1: %d points; cycles of the bases %d; relation N Psi* + q.u = 0 '
              'fails on %d (largest residue over all cycles %.2g; tolerance of a tie %g)' % (stats['points'], stats['degree_fail'], stats['cycles'],
                                                      stats['relation_fail'], stats['worst'], TOL))
        print('  points with a cycle with N != 0: %d; without: %d; cycles with N = 0 and q != 0: %d; with N = 0 and '
              'q = 0: %d' % (stats['with_N'], stats['without_N'], stats['mass_relation_cycles'],
                             stats['balanced_cycles']))
        print('  E* has: %s; sizes of E*: %s' % (dict(stats['estar_kinds']), dict(sorted(stats['estar_sizes'].items()))))
        print('  values -q.u/N of the cycles with N != 0 (count of cycles): %s'
              % dict(sorted(stats['psi_values'].items(), key=lambda kv: float(Fraction(kv[0])))))
        for ex in stats['no_N_examples'][:5]:
            print('   no cycle with N != 0: trees %s, Psi* %s, E* %s' % ex)


if __name__ == '__main__':
    main()
