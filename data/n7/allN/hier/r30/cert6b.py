"""R30: exact Farkas certificates, support-based rational solve."""
import pickle, numpy as np
from fractions import Fraction as F
from scipy.optimize import linprog
from lp6 import data, bodies, build, chamber_u, surv, n

def gauss(M, t):
    """exact solve M v = t over Q; return (particular, nullspace basis) or None"""
    rows = len(M); cols = len(M[0])
    A = [[F(int(x)) for x in M[i]] + [F(int(t[i]))] for i in range(rows)]
    piv = []
    r = 0
    for c in range(cols):
        p = next((i for i in range(r, rows) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c); r += 1
        if r == rows:
            break
    for i in range(r, rows):
        if A[i][cols] != 0:
            return None
    free = [c for c in range(cols) if c not in piv]
    part = [F(0)] * cols
    for i, c in enumerate(piv):
        part[c] = A[i][cols]
    basis = []
    for fc in free:
        v = [F(0)] * cols
        v[fc] = F(1)
        for i, c in enumerate(piv):
            v[c] = -A[i][fc]
        basis.append(v)
    return part, basis, free

def farkas_exact(iz, iw, cyc, u):
    Aeq, beq, Aub, bub = build(iz, iw, cyc, u, 0.0)
    Aeq, beq, Aub, bub = map(np.array, (Aeq, beq, Aub, bub))
    m, k = Aub.shape; me = Aeq.shape[0]; nv = k
    A = np.zeros((nv + 1, m + me))
    A[:nv, :m] = Aub.T; A[:nv, m:] = Aeq.T
    A[nv, :m] = bub; A[nv, m:] = beq
    b = np.zeros(nv + 1); b[nv] = -1.0
    bounds = [(0, None)] * m + [(None, None)] * me
    r = linprog(np.zeros(m + me), A_eq=A, b_eq=b, bounds=bounds, method="highs")
    if r.status != 0:
        return ("no-farkas-float", None)
    yz = r.x
    S = [i for i in range(m + me) if abs(yz[i]) > 1e-8]
    M = A[:, S]
    sol = gauss(M, b)
    if sol is None:
        return ("support-inconsistent", None)
    part, basis, free = sol
    # try free vars = rounded float values, then 0
    for mode in ("float", "zero"):
        v = list(part)
        for j, fc in enumerate(free):
            val = F(yz[S[fc]]).limit_denominator(10**6) if mode == "float" else F(0)
            for i in range(len(v)):
                v[i] += val * basis[j][i]
        full = [F(0)] * (m + me)
        for i, s in enumerate(S):
            full[s] = v[i]
        if all(full[j] >= 0 for j in range(m)):
            # equalities hold by construction; verify anyway
            ok = all(sum(F(int(A[i, j])) * full[j] for j in range(m + me)) == F(int(b[i]))
                     for i in range(nv + 1))
            if ok:
                return ("cert", full)
    return ("sign-fail", None)

u = chamber_u(36.0)
fails = pickle.load(open("cert6_fails.pkl", "rb"))
ncert = 0; still = []
for iz, iw, cyc in fails:
    tag, c = farkas_exact(iz, iw, cyc, u)
    if tag == "cert":
        ncert += 1
    else:
        still.append((iz, iw, cyc, tag))
print(f"newly certified: {ncert}/{len(fails)}; total {len(surv) - len(still)}/{len(surv)}")
for s in still[:10]:
    print("  still uncertified:", s)
pickle.dump(still, open("cert6_still.pkl", "wb"))
