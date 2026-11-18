"""R30 check, part C: Theorem D4 at n=4, vertices {0,1,2,3,O=4}.

Exhaustive over all hierarchy pairs (all ultrametric node structures).
For every simple cycle of G_full containing an O-edge, LP-test whether heights
can place it in E* (Psi = Psi* = max over ALL edges incl. O-edges).  For each
feasible cycle check: N != 0, N Psi* + q.u = 0, Psi* <= (2n-1) sum|u| / 3.
(All-body-pair cycles are already excluded by the n<=4 Lemma C check.)
Control: u=(0,1,2,3) must admit the note's N=0 cycle (0,2),(2,O),(0,O),(0,3).
"""
import itertools, time, collections, pickle
import numpy as np
from scipy.optimize import linprog
from check_cycles import hierarchies, simple_cycles

n = 4
V = n + 1
O = n
t0 = time.time()
hs = list(hierarchies(range(V)))
print(len(hs), "hierarchies on 5 vertices", flush=True)
pairs = [(a, b) for a in range(V) for b in range(a+1, V)]
bp = [p for p in pairs if p[1] != O]
oe = [p for p in pairs if p[1] == O]

def masks(h):
    cl = sorted(h, key=len)
    ms = [sum(1 << a for a in c) for c in cl]
    nm = {}
    for p in pairs:
        bit = (1 << p[0]) | (1 << p[1])
        nm[p] = next(i for i, m in enumerate(ms) if m & bit == bit)
    par = []
    for i, m in enumerate(ms):
        cands = [j for j, m2 in enumerate(ms) if m2 & m == m and m2 != m]
        par.append(min(cands, key=lambda j: ms[j]) if cands else None)
    return ms, nm, par

data = [masks(h) for h in hs]

def psi_row(nmz, nmw, nz, p, nv):
    row = np.zeros(nv)
    if p[1] == O:
        row[nmz[p]] = -1.0
        row[nz + nmw[p]] = -1.0
        row[-1] = 1.0          # Psi(t,O) = -hz - hw - u_t ; row.x = Psi + u_t? see below
    else:
        row[nmz[p]] = 0.5
        row[nz + nmw[p]] = 0.5
        row[-1] = -1.0
    return row

def build(iz, iw, cyc_edges, u, eps):
    mz, nmz, pz = data[iz]; mw, nmw, pw = data[iw]
    nz, nw = len(mz), len(mw)
    nv = nz + nw + 1
    Aeq, beq, Aub, bub = [], [], [], []
    for p in pairs:
        row = psi_row(nmz, nmw, nz, p, nv)
        if p[1] == O:
            # Psi(t,O) = -hz-hw-u_t  ->  -hz-hw - Psi = u_t
            r = np.zeros(nv); r[nmz[p]] = -1; r[nz+nmw[p]] = -1; r[-1] = -1
            rhs = u[p[0]]
        else:
            r = np.zeros(nv); r[nmz[p]] = 0.5; r[nz+nmw[p]] = 0.5; r[-1] = -1
            rhs = u[p[0]] + u[p[1]]
        if p in cyc_edges:
            Aeq.append(r); beq.append(rhs)
        else:
            Aub.append(r); bub.append(rhs)
    for (par, off) in ((pz, 0), (pw, nz)):
        for i, p in enumerate(par):
            if p is not None:
                r = np.zeros(nv); r[off+i] = -1; r[off+p] = 1
                Aub.append(r); bub.append(-eps)
    return np.array(Aeq), np.array(beq), np.array(Aub), np.array(bub)

def Nq(cyc, s0):
    N = 0; q = [0]*n
    for i, p in enumerate(cyc):
        s = s0 * (1 if i % 2 == 0 else -1)
        if p[1] == O:
            q[p[0]] -= s
        else:
            N += 3 * s
            q[p[0]] += 2*s; q[p[1]] += 2*s
    return N, q

def run(u, label, eps=0.0, cert=False):
    nfeas = 0; bad = []; n0 = []; seen = set(); nlp = 0
    bound = (2*n - 1) * sum(abs(x) for x in u) / 3
    for iz in range(len(hs)):
        mz, nmz, pz = data[iz]
        for iw in range(len(hs)):
            mw, nmw, pw = data[iw]
            edges = [(nmz[p], nmw[p]) for p in pairs]
            for cyc in simple_cycles(edges, len(mz), len(mw)):
                cp = tuple(pairs[k] for k in cyc)
                if all(p[1] != O for p in cp):
                    continue  # body-only: excluded by Lemma C check
                key = (iz, iw, frozenset(cp))
                if key in seen:
                    continue
                seen.add(key)
                nlp += 1
                Aeq, beq, Aub, bub = build(iz, iw, set(cp), u, eps)
                r = linprog(np.zeros(Aeq.shape[1]), A_ub=Aub, b_ub=bub,
                            A_eq=Aeq, b_eq=beq,
                            bounds=[(None, None)]*Aeq.shape[1], method="highs")
                if r.status != 0:
                    continue
                nfeas += 1
                psi = r.x[-1]
                for s0 in (1, -1):
                    N, q = Nq(cp, s0)
                    rel = N * psi + sum(q[j]*u[j] for j in range(n))
                    if abs(rel) > 1e-6 * max(1, abs(N*psi)):
                        bad.append(("relation", iz, iw, cp, N, q, rel))
                    if psi > bound + 1e-6:
                        bad.append(("bound", iz, iw, cp, psi, bound))
                    if N == 0:
                        n0.append((iz, iw, cp, q))
        if iz % 50 == 0:
            print(f"  {label} iz={iz} {time.time()-t0:.0f}s lp={nlp} feas={nfeas} N0={len(n0)} bad={len(bad)}", flush=True)
    print(f"{label}: LPs={nlp}, feasible={nfeas}, N=0 cases={len(n0)}, violations={len(bad)}")
    for b in bad[:5]:
        print("  VIOLATION:", b)
    for z in n0[:5]:
        print("  N=0:", z)
    return n0, bad

u_ch = np.array([0.0, 1.0, 34.0, 1156.0])  # W_4(32): gaps 1, 33>32, 1122>1088
n0, bad = run(u_ch, "chamber u=(0,1,34,1156)")
pickle.dump((n0, bad), open("d4n4_chamber.pkl", "wb"))
u_ctl = np.array([0.0, 1.0, 2.0, 3.0])
n0c, badc = run(u_ctl, "control u=(0,1,2,3)")
pickle.dump((n0c, badc), open("d4n4_control.pkl", "wb"))
print(f"total {time.time()-t0:.0f}s")
