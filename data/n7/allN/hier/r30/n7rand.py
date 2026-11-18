"""R30: randomized Lemma C stress test at n=7 (and n=8), chamber u."""
import random, time, numpy as np
from scipy.optimize import linprog
from check_cycles import hierarchies, simple_cycles, qvec

def masks(h, n, bodies):
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

def c1_ok(cyc, bodies, mz, mw, nmz, nmw, n):
    for k in cyc:
        c, d = bodies[k]
        inter = mz[nmz[(c,d)]] & mw[nmw[(c,d)]]
        for a in range(n):
            if a != c and a != d and a <= max(c,d) and (inter >> a) & 1:
                return False
    return True

def lpfeas(iz, iw, cyc, u, data, bodies, n, eps=0.0):
    mz,nmz,pz = iz; mw,nmw,pw = iw
    nz,nw = len(mz),len(mw); nv = nz+nw+1
    Aeq=[];beq=[];Aub=[];bub=[]
    for f in bodies:
        a,b=f
        r=np.zeros(nv); r[nmz[f]]=0.5; r[nz+nmw[f]]=0.5; r[-1]=-1
        if f in cyc: Aeq.append(r); beq.append(u[a]+u[b])
        else: Aub.append(r); bub.append(u[a]+u[b])
    for par,off in ((pz,0),(pw,nz)):
        for i,p in enumerate(par):
            if p is not None:
                r=np.zeros(nv); r[off+i]=-1; r[off+p]=1
                Aub.append(r); bub.append(-eps)
    r=linprog(np.zeros(nv),A_ub=np.array(Aub),b_ub=np.array(bub),
              A_eq=np.array(Aeq),b_eq=np.array(beq),bounds=[(None,None)]*nv,method="highs")
    return r.status==0

for n, trials, seed in ((7, 150000, 7), (8, 60000, 8)):
    t0=time.time()
    hs=list(hierarchies(range(n)))
    bodies=[(a,b) for a in range(n) for b in range(a+1,n)]
    md=[masks(h,n,bodies) for h in hs]
    rng=random.Random(seed)
    u=np.array([0.0]+[0.0]*(n-1))
    for j in range(1,n): u[j]=u[j-1]+(n*n+1)*u[j-1]+1
    nsurv=0; nfeas=0; nbal=0
    for t in range(trials):
        iz=rng.randrange(len(hs)); iw=rng.randrange(len(hs))
        mz,nmz,pz=md[iz]; mw,nmw,pw=md[iw]
        passes=False
        for L in range(n-1,1,-1):
            ok=0; low=(1<<L)-1
            for x in range(L):
                p=(x,L)
                if mz[nmz[p]] & mw[nmw[p]] & low & ~(1<<x) == 0:
                    ok+=1
                    if ok>=2: break
            if ok>=2: passes=True; break
        if not passes: continue
        edges=[(nmz[p],nmw[p]) for p in bodies]
        for cyc in simple_cycles(edges,len(mz),len(mw)):
            if any(qvec(cyc,bodies,n,1)): continue
            nbal+=1
            if not c1_ok(cyc,bodies,mz,mw,nmz,nmw,n): continue
            nsurv+=1
            cp=set(bodies[k] for k in cyc)
            if lpfeas(md[iz],md[iw],cp,u,md,bodies,n):
                nfeas+=1
                print("FEASIBLE balanced C1 cycle in chamber!", n, iz, iw, sorted(cp), flush=True)
    print(f"n={n}: {trials} random pairs, {nbal} balanced, {nsurv} pass C1, "
          f"{nfeas} height-feasible in chamber, {time.time()-t0:.0f}s", flush=True)
