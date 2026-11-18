"""R30 check, part A2 (fixed enumerator).

For every pair of hierarchies (all ultrametric node structures) on n bodies:
enumerate simple cycles of G_full; keep those that are
  (i) balanced: q = sum (-1)^i (1_a+1_b) = 0  (necessary in chamber, by C2),
  (ii) C1-consistent with the chamber order u_0 < ... < u_{n-1}:
       for each cycle edge (c,d), every other body of Z_e cap W_e has index
       > max(c,d).
Any simple cycle of B^o in the chamber must pass both.  Survivors are then
LP-tested for height realizability (all cycle edges in E^o) in part B.
"""
import sys, itertools, time, pickle, collections
from check_cycles import hierarchies, node_map, simple_cycles, qvec

def c1_ok(cyc, bodies, cz, cw, nmz, nmw):
    for k in cyc:
        c, d = bodies[k]
        Z = cz[nmz[(c, d)]]; W = cw[nmw[(c, d)]]
        for a in Z & W:
            if a != c and a != d and a <= max(c, d):
                return False
    return True

def run(n):
    t0 = time.time()
    hs = list(hierarchies(range(n)))
    data = [node_map(h, n) for h in hs]
    bodies = [(a, b) for a in range(n) for b in range(a+1, n)]
    surv = []
    nbal = 0
    for iz in range(len(hs)):
        nmz, cz = data[iz]
        for iw in range(len(hs)):
            nmw, cw = data[iw]
            edges = [(nmz[p], nmw[p]) for p in bodies]
            for cyc in simple_cycles(edges, len(cz), len(cw)):
                # balance is parity-class invariant up to sign; test one
                q = qvec(cyc, bodies, n, 1)
                if any(q):
                    continue
                nbal += 1
                if c1_ok(cyc, bodies, cz, cw, nmz, nmw):
                    surv.append((iz, iw, cyc))
        if n >= 6 and iz % 400 == 0:
            print(f"  iz={iz} {time.time()-t0:.0f}s bal={nbal} surv={len(surv)}", flush=True)
    print(f"n={n}: {len(hs)} hierarchies, {len(hs)**2} pairs, "
          f"{nbal} balanced cycles, {len(surv)} pass C1, {time.time()-t0:.0f}s", flush=True)
    # abstract survivor shapes (edge sets of bodies, up to parity)
    shapes = collections.Counter()
    for iz, iw, cyc in surv:
        es = frozenset(bodies[k] for k in cyc)
        shapes[(len(cyc), es)] += 1
    print(f"  distinct abstract (length, edge-set) survivors: {len(shapes)}")
    for (L, es), c in list(shapes.items())[:12]:
        print("   ", L, sorted(es), "x", c)
    pickle.dump((hs, surv), open(f"surv{n}.pkl", "wb"))
    return surv

if __name__ == "__main__":
    run(int(sys.argv[1]))
