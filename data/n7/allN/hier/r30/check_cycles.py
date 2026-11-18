"""R30 independent check, part A.

Enumerate ALL ultrametric node structures (hierarchies / laminar families) on n
labeled bodies, n = 3..5.  For every pair (zeta-hierarchy, omega-hierarchy):
  - build the full bipartite multigraph G_full: one edge per body pair, between
    its zeta-node and its omega-node (B^o of the note is a subgraph of this);
  - enumerate all simple cycles;
  - for each of the two parity numberings compute q = sum (-1)^i (1_a + 1_b);
  - report balanced cycles (q = 0).

Lemma C (C2) says: in the chamber, every simple cycle of B^o is balanced.
So if G_full has NO balanced simple cycle, no B^o cycle exists in the chamber,
for ANY heights.  This is an exhaustive check of Lemma C for n <= 5, over all
ultrametrics (ties included: a hierarchy with strictly monotone heights
represents every ultrametric, equal-height nodes merged).
"""
import sys, itertools, time
from functools import lru_cache

def partitions(set_):
    """all set partitions into >= 2 blocks"""
    items = sorted(set_)
    if len(items) < 2:
        return
    first, rest = items[0], items[1:]
    for p in partitions_recursive(rest):
        # first alone
        yield [frozenset([first])] + p
        # first inserted into each block
        for i, b in enumerate(p):
            yield p[:i] + [b | {first}] + p[i+1:]

def partitions_recursive(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in partitions_recursive(rest):
        yield [frozenset([first])] + p
        for i, b in enumerate(p):
            yield p[:i] + [b | {first}] + p[i+1:]

def hierarchies(leaves):
    """all laminar families of clusters (size>=2) incl. the full set"""
    leaves = frozenset(leaves)
    if len(leaves) == 1:
        yield frozenset()
        return
    for part in partitions(leaves):
        if len(part) < 2:
            continue
        for combo in itertools.product(*[list(hierarchies(b)) for b in part]):
            yield frozenset([leaves]).union(*combo)

def node_map(hier, n):
    """pair -> smallest cluster containing it (index into sorted cluster list)"""
    clusters = sorted(hier, key=len)
    nm = {}
    for a in range(n):
        for b in range(a+1, n):
            for i, c in enumerate(clusters):
                if a in c and b in c:
                    nm[(a, b)] = i
                    break
    return nm, clusters

def simple_cycles(edges, nZ, nW):
    """edges: list (znode, wnode).  yield canonical simple cycles as tuples of
    edge indices, cyclic order, both directions / rotations identified.
    Vertices: z-nodes 0..nZ-1, w-nodes offset nZ.  r>=1 (2-cycles allowed)."""
    adjZ = [[] for _ in range(nZ)]
    adjW = [[] for _ in range(nW)]
    for k, (z, w) in enumerate(edges):
        adjZ[z].append((w, k))
        adjW[w].append((z, k))
    seen = set()
    m = len(edges)
    for start in range(m):
        z0, w0 = edges[start]
        # alternating DFS: z0 -start-> w0 -k-> z1 -k'-> w1 ...
        # a simple cycle closes only at z0, from a w-vertex, even length
        def rec_w(wcur, eseq, verts):
            for znext, k in adjW[wcur]:
                if k in eseq:
                    continue
                if znext == z0:
                    cyc = eseq + (k,)
                    if len(cyc) % 2 == 0:
                        canon = canonical(cyc)
                        if canon not in seen:
                            seen.add(canon)
                            yield canon
                    continue
                if znext in verts:
                    continue
                yield from rec_z(znext, eseq + (k,), verts | {znext})
        def rec_z(zcur, eseq, verts):
            for wnext, k in adjZ[zcur]:
                if k in eseq:
                    continue
                if nZ + wnext in verts:
                    continue
                yield from rec_w(wnext, eseq + (k,), verts | {nZ + wnext})
        yield from rec_w(w0, (start,), frozenset([z0, nZ + w0]))

def canonical(cyc):
    L = len(cyc)
    rots = []
    for i in range(0, L, 2):  # rotations preserving bipartite parity
        rots.append(tuple(cyc[i:] + cyc[:i]))
    rev = tuple(reversed(cyc))
    for i in range(0, L, 2):
        rots.append(tuple(rev[i:] + rev[:i]))
    return min(rots)

def qvec(cyc, edges_bodies, n, sign0):
    q = [0]*n
    for i, k in enumerate(cyc):
        s = sign0 * (1 if i % 2 == 0 else -1)
        a, b = edges_bodies[k]
        q[a] += s; q[b] += s
    return tuple(q)

def run(n, max_pairs=None, seed=0):
    t0 = time.time()
    hs = list(hierarchies(range(n)))
    print(f"n={n}: {len(hs)} hierarchies, {len(hs)**2} pairs", flush=True)
    data = [node_map(h, n) for h in hs]
    bodies = [(a, b) for a in range(n) for b in range(a+1, n)]
    balanced = []
    npairs = 0
    import random
    rng = random.Random(seed)
    pairs_iter = itertools.product(range(len(hs)), repeat=2)
    if max_pairs:
        pairs_iter = ((rng.randrange(len(hs)), rng.randrange(len(hs)))
                      for _ in range(max_pairs))
    for iz, iw in pairs_iter:
        npairs += 1
        nmz, cz = data[iz]; nmw, cw = data[iw]
        edges = [(nmz[p], nmw[p]) for p in bodies]
        for cyc in simple_cycles(edges, len(cz), len(cw)):
            for s0 in (1, -1):
                q = qvec(cyc, bodies, n, s0)
                if not any(q):
                    balanced.append((iz, iw, cyc, q))
    print(f"n={n}: {npairs} hierarchy pairs checked, "
          f"{len(balanced)} balanced simple cycles found, "
          f"{time.time()-t0:.1f}s", flush=True)
    return balanced, hs, data, bodies

if __name__ == "__main__":
    n = int(sys.argv[1])
    mp = int(sys.argv[2]) if len(sys.argv) > 2 else None
    bal, *_ = run(n, mp)
    for b in bal[:10]:
        print("  balanced:", b)
