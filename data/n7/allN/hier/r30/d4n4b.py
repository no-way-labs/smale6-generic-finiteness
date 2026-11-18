"""R30 D4 n=4 sweep, corrected monotonicity, all cyclic orders checked."""
import numpy as np, collections, pickle, time
from scipy.optimize import linprog
src = open("d4n4.py").read().split("u_ch = ")[0]
g = {}; exec(src, g)
hs, data, pairs, simple_cycles, build, Nq = (g[k] for k in
    ("hs","data","pairs","simple_cycles","build","Nq"))
n, O = 4, 4
t0 = time.time()

def run(u, label):
    groups = collections.defaultdict(list)
    for iz in range(len(hs)):
        mz,nmz,pz = data[iz]
        for iw in range(len(hs)):
            mw,nmw,pw = data[iw]
            edges=[(nmz[p],nmw[p]) for p in pairs]
            for cyc in simple_cycles(edges,len(mz),len(mw)):
                cp = tuple(pairs[k] for k in cyc)
                if all(p[1]!=O for p in cp): continue
                groups[(iz,iw,frozenset(cp))].append(cp)
    print(f"{label}: {len(groups)} distinct (pair, edge-set) groups", flush=True)
    nfeas=0; bad=[]; n0=[]; psivals=collections.Counter(); nlp=0
    bound = (2*n-1)*sum(abs(x) for x in u)/3
    for (iz,iw,es), orders in groups.items():
        nlp+=1
        Aeq,beq,Aub,bub = build(iz,iw,es,u,0.0)
        r=linprog(np.zeros(Aeq.shape[1]),A_ub=Aub,b_ub=bub,A_eq=Aeq,b_eq=beq,
                  bounds=[(None,None)]*Aeq.shape[1],method="highs")
        if r.status!=0: continue
        nfeas+=1
        psi=r.x[-1]; psivals[round(psi,6)]+=1
        for cp in orders:
            for s0 in (1,-1):
                N,q=Nq(cp,s0)
                rel=N*psi+sum(q[j]*u[j] for j in range(n))
                if abs(rel)>1e-6*max(1,abs(N*psi)):
                    bad.append(("relation",iz,iw,cp,N,q,rel))
                if psi>bound+1e-6:
                    bad.append(("bound",iz,iw,cp,psi,bound))
                if N==0: n0.append((iz,iw,cp,q))
    print(f"{label}: LPs={nlp} feasible={nfeas} N0={len(n0)} violations={len(bad)} "
          f"distinct psi={len(psivals)} max psi={max(psivals) if psivals else None} "
          f"bound={bound:.1f} {time.time()-t0:.0f}s", flush=True)
    for b in bad[:5]: print("  VIOLATION:",b)
    return n0,bad,psivals,groups

u_ch=np.array([0.,1.,34.,1156.])
n0,bad,psivals,groups = run(u_ch,"chamber")
print("psi values:", sorted(psivals.items()))
pickle.dump((n0,bad,psivals),open("d4n4b_chamber.pkl","wb"))
u_ctl=np.array([0.,1.,2.,3.])
n0c,badc,psivalsc,_ = run(u_ctl,"control")
tgt={(0,2),(2,4),(0,4),(0,3)}
hits=[z for z in n0c if set(z[2])==tgt]
print("note's control cycle among N=0:",len(hits), hits[0] if hits else None)
pickle.dump((n0c,badc),open("d4n4b_control.pkl","wb"))
