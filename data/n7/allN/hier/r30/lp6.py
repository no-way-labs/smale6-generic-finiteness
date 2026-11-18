"""R30 check, part B: LP height-realizability of the n=6 survivors.

For each survivor (zeta-hierarchy, omega-hierarchy, hexagon), ask whether real
heights exist with all six hexagon edges in E^o (Psi = Psi^o = max).  Variables:
cluster heights (strictly decreasing up each hierarchy) and Psi^o.  All
constraints linear.  Lemma C predicts INFEASIBLE for u in W_6(36).
Controls: u outside the chamber should admit feasible points.

eps=0 (non-strict) infeasibility is the strong statement: any true ultrametric
counterexample merges equal-height nodes into a coarser hierarchy, which is
also in our exhaustive list, with strict gaps there.
"""
import pickle, itertools, numpy as np
from scipy.optimize import linprog
from check_cycles import hierarchies

n = 6
hs, surv = pickle.load(open("surv6.pkl", "rb"))
bodies = [(a, b) for a in range(n) for b in range(a+1, n)]

def masks(h):
    cl = sorted(h, key=len)
    ms = [sum(1 << a for a in c) for c in cl]
    nm = {}
    for p in bodies:
        bit = (1 << p[0]) | (1 << p[1])
        nm[p] = next(i for i, m in enumerate(ms) if m & bit == bit)
    par = []
    for i, m in enumerate(ms):
        cands = [j for j, m2 in enumerate(ms) if m2 & m == m and m2 != m]
        par.append(min(cands, key=lambda j: ms[j]) if cands else None)
    return ms, nm, par

data = [masks(h) for h in hs]

def chamber_u(tau):
    u = [0.0]
    for j in range(1, n):
        u.append(u[-1] + (tau + 1.0) * u[-1] + 1.0)
    return np.array(u)

def build(iz, iw, cyc, u, eps):
    mz, nmz, pz = data[iz]; mw, nmw, pw = data[iw]
    nz, nw = len(mz), len(mw)
    nv = nz + nw + 1
    ip = nz + nw
    Aeq, beq = [], []
    for k in cyc:
        a, b = bodies[k]
        row = np.zeros(nv)
        row[nmz[(a, b)]] = 1.0
        row[nz + nmw[(a, b)]] = 1.0
        row[ip] = -2.0
        Aeq.append(row); beq.append(2.0 * (u[a] + u[b]))
    Aub, bub = [], []
    for f in bodies:
        a, b = f
        row = np.zeros(nv)
        row[nmz[f]] = 1.0
        row[nz + nmw[f]] = 1.0
        row[ip] = -2.0
        Aub.append(row); bub.append(2.0 * (u[a] + u[b]))
    for (par, off, cnt) in ((pz, 0, nz), (pw, nz, nw)):
        for i, p in enumerate(par):
            if p is not None:
                row = np.zeros(nv)
                row[off + i] = -1.0
                row[off + p] = 1.0
                Aub.append(row); bub.append(-eps)
    return Aeq, beq, Aub, bub

def solve(iz, iw, cyc, u, eps):
    Aeq, beq, Aub, bub = build(iz, iw, cyc, u, eps)
    r = linprog(np.zeros(len(Aeq[0])), A_ub=np.array(Aub), b_ub=np.array(bub),
                A_eq=np.array(Aeq), b_eq=np.array(beq),
                bounds=[(None, None)] * len(Aeq[0]), method="highs")
    return r

us = {
    "chamber tau=36": chamber_u(36.0),
    "chamber tau=37": chamber_u(37.0),
    "mild (0,1,2,3,4,5)": np.arange(6.0),
    "equal u=0": np.zeros(6),
    "geom 2^j": np.array([2.0**j for j in range(6)]),
}
for name, u in us.items():
    feas = []
    for iz, iw, cyc in surv:
        r = solve(iz, iw, cyc, u, 0.0)
        if r.status == 0:
            feas.append((iz, iw, cyc, r.x))
    print(f"u={name}: {len(feas)}/{len(surv)} survivors feasible (eps=0)", flush=True)
    if feas and name.startswith("chamber"):
        iz, iw, cyc, x = feas[0]
        print("  COUNTEREXAMPLE?", iz, iw, [bodies[k] for k in cyc], x)
    if feas and not name.startswith("chamber"):
        # verify one feasible point exactly-ish: recompute Psi and nodes
        iz, iw, cyc, x = feas[0]
        mz, nmz, pz = data[iz]; mw, nmw, pw = data[iw]
        nz = len(mz)
        psi = x[-1]
        Ps = {}
        for f in bodies:
            a, b = f
            Ps[f] = (x[nmz[f]] + x[nz + nmw[f]]) / 2 - u[a] - u[b]
        mx = max(Ps.values())
        print("  example feasible:", [bodies[k] for k in cyc],
              "all cycle edges at max:", all(abs(Ps[bodies[k]] - mx) < 1e-7 for k in cyc))
