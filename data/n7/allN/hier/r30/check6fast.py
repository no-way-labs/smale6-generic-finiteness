"""R30 check, n=6, optimized.

Pre-filter: in a balanced C1-consistent cycle every body has even degree >= 2.
Body 5 (lightest) lies in >= 2 cycle edges (5,x); C1 forces Z(5,x) cap W(5,x)
= {5,x} for each (no body is lighter than 5).  So a pair can host a survivor
only if >= 2 partners x have 2-element intersection.  Cheap bitmask test.
"""
import itertools, time, pickle, collections
from check_cycles import hierarchies, simple_cycles, qvec

def c1_ok(cyc, bodies, mz, mw, nmz, nmw):
    for k in cyc:
        c, d = bodies[k]
        inter = mz[nmz[(c, d)]] & mw[nmw[(c, d)]]
        for a in range(6):
            if a != c and a != d and a <= max(c, d) and (inter >> a) & 1:
                return False
    return True

n = 6
t0 = time.time()
hs = list(hierarchies(range(n)))
print(len(hs), "hierarchies", flush=True)

def masks(h):
    cl = sorted(h, key=len)
    ms = [sum(1 << a for a in c) for c in cl]
    nm = {}
    for a in range(n):
        for b in range(a+1, n):
            bit = (1 << a) | (1 << b)
            for i, m in enumerate(ms):
                if m & bit == bit:
                    nm[(a, b)] = i
                    break
    return ms, nm

data = [masks(h) for h in hs]
bodies = [(a, b) for a in range(n) for b in range(a+1, n)]
p5 = [(5, x) for x in range(5)]  # (x,5) keys
surv = []
nbal = 0
npass = 0
for iz in range(len(hs)):
    mz, nmz = data[iz]
    for iw in range(len(hs)):
        mw, nmw = data[iw]
        # necessary: for L = max-index body of the cycle (even degree >= 2),
        # >= 2 partners x < L with Z(x,L) cap W(x,L) containing no body of
        # index <= L besides x, L  (C1: others must be lighter than L).
        passes = False
        for L in range(5, 1, -1):
            ok = 0
            lowmask = (1 << L) - 1  # bits 0..L-1
            for x in range(L):
                p = (x, L)
                inter = mz[nmz[p]] & mw[nmw[p]]
                if inter & lowmask & ~(1 << x) == 0:
                    ok += 1
                    if ok >= 2:
                        break
            if ok >= 2:
                passes = True
                break
        if not passes:
            continue
        npass += 1
        edges = [(nmz[p], nmw[p]) for p in bodies]
        for cyc in simple_cycles(edges, len(mz), len(mw)):
            if any(qvec(cyc, bodies, n, 1)):
                continue
            nbal += 1
            if c1_ok(cyc, bodies, mz, mw, nmz, nmw):
                surv.append((iz, iw, cyc))
    if iz % 400 == 0:
        print(f"iz={iz} {time.time()-t0:.0f}s pass={npass} bal={nbal} surv={len(surv)}", flush=True)

print(f"pairs passing filter: {npass}; balanced among them: {nbal}; survivors: {len(surv)}")
shapes = collections.Counter()
for iz, iw, cyc in surv:
    shapes[frozenset(bodies[k] for k in cyc)] += 1
print("distinct abstract edge-sets:", len(shapes))
for es, c in shapes.items():
    print("  ", sorted(es), "x", c)
print("lengths:", collections.Counter(len(c) for _, _, c in surv))
print("bodies used:", collections.Counter(len(set(x for k in c for x in bodies[k])) for _, _, c in surv))
pickle.dump((hs, surv), open("surv6.pkl", "wb"))
print(f"{time.time()-t0:.0f}s")
