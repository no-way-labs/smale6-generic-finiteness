import time, collections, itertools
from check_cycles import hierarchies, node_map, simple_cycles, qvec

n = 6
t0 = time.time()
hs = list(hierarchies(range(n)))
print(len(hs), "hierarchies", flush=True)
data = [node_map(h, n) for h in hs]
bodies = [(a,b) for a in range(n) for b in range(a+1,n)]
cnt = collections.Counter()
examples = {}
tot = 0
for iz in range(len(hs)):
    nmz, cz = data[iz]
    for iw in range(len(hs)):
        nmw, cw = data[iw]
        edges = [(nmz[p], nmw[p]) for p in bodies]
        for cyc in simple_cycles(edges, len(cz), len(cw)):
            for s0 in (1,-1):
                q = qvec(cyc, bodies, n, s0)
                if not any(q):
                    used = frozenset(x for k in cyc for x in bodies[k])
                    key = (len(cyc), len(used))
                    cnt[key] += 1
                    examples.setdefault(key, (iz, iw, cyc))
                    tot += 1
    if iz % 400 == 0:
        print(iz, f"{time.time()-t0:.0f}s", dict(cnt), flush=True)
print("TOTAL balanced (cycle, parity) instances:", tot)
print("by (length, #bodies):", dict(cnt))
# distinct abstract balanced hexagons: edge sets of bodies
abs_hex = set()
for key,(iz,iw,cyc) in examples.items():
    pass
print(f"{time.time()-t0:.0f}s")
import pickle
pickle.dump((cnt, examples), open("bal6.pkl","wb"))
