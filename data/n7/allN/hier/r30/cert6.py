"""R30: random chamber vectors + exact Farkas certificates for n=6 Lemma C."""
import pickle, numpy as np, random
from fractions import Fraction as F
from scipy.optimize import linprog
from lp6 import data, bodies, build, chamber_u, surv, n

rng = random.Random(30)
def rand_chamber(tau):
    u = [0]
    for j in range(1, n):
        gap = rng.randint(int(tau * u[-1]) + 1, int((tau + 5) * u[-1]) + 2)
        u.append(u[-1] + gap)
    return np.array(u, dtype=float)

print("random chamber tests (eps=0):")
for t in range(5):
    u = rand_chamber(36.0)
    nf = 0
    for iz, iw, cyc in surv:
        Aeq, beq, Aub, bub = build(iz, iw, cyc, u, 0.0)
        r = linprog(np.zeros(len(Aeq[0])), A_ub=np.array(Aub), b_ub=np.array(bub),
                    A_eq=np.array(Aeq), b_eq=np.array(beq),
                    bounds=[(None, None)] * len(Aeq[0]), method="highs")
        nf += (r.status == 0)
    print(f"  u={list(u.astype(int))}: feasible {nf}/{len(surv)}")

def farkas_exact(iz, iw, cyc, u):
    Aeq, beq, Aub, bub = build(iz, iw, cyc, u, 0.0)
    Aeq, beq, Aub, bub = map(np.array, (Aeq, beq, Aub, bub))
    m, k = Aub.shape
    me = Aeq.shape[0]
    nv = k
    # variables: y (m, >=0), z (me, free)
    # A_ub^T y + A_eq^T z = 0 ; b_ub.y + b_eq.z = -1
    A = np.zeros((nv + 1, m + me))
    A[:nv, :m] = Aub.T
    A[:nv, m:] = Aeq.T
    A[nv, :m] = bub
    A[nv, m:] = beq
    b = np.zeros(nv + 1); b[nv] = -1.0
    bounds = [(0, None)] * m + [(None, None)] * me
    r = linprog(np.zeros(m + me), A_eq=A, b_eq=b, bounds=bounds, method="highs")
    if r.status != 0:
        return None
    yz = r.x
    # rationalize and verify exactly
    yr = [F(v).limit_denominator(10**6) for v in yz]
    ok = all(v >= 0 for v in yr[:m])
    if not ok:
        return None
    for i in range(nv):
        s = sum(F(int(Aub[j, i])) * yr[j] for j in range(m)) + \
            sum(F(int(Aeq[j, i])) * yr[m + j] for j in range(me))
        if s != 0:
            return None
    s = sum(F(int(bub[j])) * yr[j] for j in range(m)) + \
        sum(F(int(beq[j])) * yr[m + j] for j in range(me))
    if s >= 0:
        return None
    return yr

u = chamber_u(36.0)
assert all(float(int(v)) == v for v in u)
ncert = 0
fails = []
for iz, iw, cyc in surv:
    c = farkas_exact(iz, iw, cyc, u)
    if c is None:
        fails.append((iz, iw, cyc))
    else:
        ncert += 1
print(f"exact rational Farkas certificates: {ncert}/{len(surv)} at u={list(u.astype(int))}")
if fails:
    print("uncertified:", fails[:5])
pickle.dump(fails, open("cert6_fails.pkl", "wb"))
