"""R29, common code.  Written for this referee round; it imports nothing from scripts/allN.

Vertices: the bodies 0, ..., n - 1 and the origin O = n.  An edge is a pair (a, b), a < b, of vertices.
A weight point is two dicts Z, W over the edges (values float, or INF for a position equal to 0), and u.
Signs as in docs/allN-direct-route.md section 1: Z[(t, l)] = v(X_t - X_l), Z[(t, O)] = v(X_t), the same for W
with Y, u_t = v(m_t), v(P_tl) = -(Z + W)/2.  The "value" of a term is minus its valuation.
"""
from itertools import combinations

INF = float('inf')


def pr(a, b):
    return (a, b) if a < b else (b, a)


def edges(n):
    return list(combinations(range(n + 1), 2))


def subsets(n):
    """nonempty sets of bodies"""
    out = []
    for r in range(1, n + 1):
        out += [frozenset(c) for c in combinations(range(n), r)]
    return out


# ---------------------------------------------------------------- trees
def _insert(t, x):
    res = [(t, x)]
    if isinstance(t, tuple):
        a, b = t
        res += [(a2, b) for a2 in _insert(a, x)]
        res += [(a, b2) for b2 in _insert(b, x)]
    return res


def all_binary_trees(leaves):
    """all rooted binary trees on the labelled leaves, as nested pairs; (2m - 3)!! of them"""
    leaves = list(leaves)
    trees = [leaves[0]]
    for x in leaves[1:]:
        new = []
        for t in trees:
            new += _insert(t, x)
        trees = new
    return trees


def tree_struct(t):
    """parent[i] of the inner node i (root 0, parent -1) and lca[(a, b)] = index of the inner node"""
    parent, lca = [], {}

    def rec(s, par):
        if not isinstance(s, tuple):
            return [s]
        i = len(parent)
        parent.append(par)
        L = rec(s[0], i)
        R = rec(s[1], i)
        for a in L:
            for b in R:
                lca[pr(a, b)] = i
        return L + R
    rec(t, -1)
    return parent, lca


# ---------------------------------------------------------------- values at a weight point
def psi(n, u, Z, W, e):
    a, b = e
    if b == n:
        if Z[e] == INF or W[e] == INF:
            return -INF
        return -Z[e] - W[e] - u[a]
    return (Z[e] + W[e]) / 2 - u[a] - u[b]


def term_value(n, u, Z, W, e, col):
    """minus the valuation of the term of the edge e in a cut generator of colour col; None if the term is 0.
    Written from the monomials: m_t X_t for an O-edge, m_a m_b P_ab^3 X_ab for a pair (Y in colour w)."""
    a, b = e
    own = Z if col == 'z' else W
    if b == n:
        if own[e] == INF:
            return None
        return -(u[a] + own[e])
    vP = -(Z[e] + W[e]) / 2
    return -(u[a] + u[b] + 3 * vP + own[e])


def crossing(n, S):
    """edges between the set S of bodies and its complement in the n + 1 vertices"""
    return [(a, b) for (a, b) in edges(n) if (a in S) != (b in S)]


def is_ultra(n, D, tol):
    for a, b, c in combinations(range(n + 1), 3):
        v = sorted([D[pr(a, b)], D[pr(a, c)], D[pr(b, c)]])
        if v[0] == INF:
            continue
        if v[1] == INF or v[1] - v[0] > tol:
            return False
    return True


def cut_failures(n, u, Z, W, tol):
    """list of (S, colour) whose largest term value is not attained twice"""
    bad = []
    for S in subsets(n):
        for col in 'zw':
            vals = [term_value(n, u, Z, W, e, col) for e in crossing(n, S)]
            vals = sorted(v for v in vals if v is not None)
            if len(vals) < 2 or vals[-1] - vals[-2] > tol:
                bad.append((sorted(S), col))
    return bad


def node_of(n, D, e, tol):
    """the clade of the node of the edge e in the tree of D: the ball of an end of e at the height D[e]"""
    a, b = e
    h = D[e]
    return frozenset([a] + [x for x in range(n + 1) if x != a and D[pr(a, x)] >= h - tol])


def analyse(n, u, Z, W, tol):
    """E*, the graph B, the degrees, all simple cycles with N and q, Lemma 19 with the leaf O, Lemma 22"""
    E = edges(n)
    P = {e: psi(n, u, Z, W, e) for e in E}
    pstar = max(P.values())
    Es = [e for e in E if pstar - P[e] <= tol]
    zn = {e: node_of(n, Z, e, tol) for e in Es}
    wn = {e: node_of(n, W, e, tol) for e in Es}
    res = {'psistar': pstar, 'Estar': Es, 'fail': []}
    # degrees
    deg = {}
    for e in Es:
        deg[('z', zn[e])] = deg.get(('z', zn[e]), 0) + 1
        deg[('w', wn[e])] = deg.get(('w', wn[e]), 0) + 1
    res['mindeg'] = min(deg.values())
    if res['mindeg'] < 2:
        res['fail'].append('a vertex of B of degree 1')
    # Lemma 22 for the body pairs of E*
    for (c, d) in Es:
        if d == n:
            continue
        common = [x for x in (zn[(c, d)] & wn[(c, d)]) if x not in (c, d, n)]
        if any(u[x] < max(u[c], u[d]) - tol for x in common):
            res['fail'].append('Lemma 22 at %s' % ((c, d),))
    # simple cycles of the bipartite multigraph B
    adj = {}
    for i, e in enumerate(Es):
        adj.setdefault(('z', zn[e]), []).append((i, ('w', wn[e])))
        adj.setdefault(('w', wn[e]), []).append((i, ('z', zn[e])))
    verts = sorted(adj, key=lambda v: (v[0], sorted(v[1])))
    rank = {v: i for i, v in enumerate(verts)}
    cycles = {}

    def dfs(v0, v, path, seen):
        for i, w in adj[v]:
            if i in path:
                continue
            if w == v0 and len(path) >= 1:
                key = frozenset(path + [i])
                cycles.setdefault(key, path + [i])
            elif rank[w] > rank[v0] and w not in seen:
                dfs(v0, w, path + [i], seen | {w})
    for v0 in verts:
        dfs(v0, v0, [], {v0})
    out = []
    for key, seq in cycles.items():
        N = 0
        q = [0] * n
        s = 0.0
        for j, i in enumerate(seq):
            sg = -1 if j % 2 == 0 else 1          # (-1)^i with i = j + 1
            a, b = Es[i]
            s += sg * (Z[Es[i]] + W[Es[i]])
            if b == n:
                q[a] -= sg
            else:
                N += 3 * sg
                q[a] += 2 * sg
                q[b] += 2 * sg
        rel = N * pstar + sum(qi * ui for qi, ui in zip(q, u))
        out.append({'edges': [Es[i] for i in seq], 'N': N, 'q': q, 'rel': rel, 'alt': s})
        if abs(s) > 10 * tol:
            res['fail'].append('alternating sum of zeta + omega not 0 on a cycle')
        if abs(rel) > 30 * tol:
            res['fail'].append('N Psi* + q.u not 0 on a cycle')
        if N == 0:
            res['fail'].append('a cycle with N = 0')
    res['cycles'] = out
    if not out:
        res['fail'].append('B has no cycle')
    return res
