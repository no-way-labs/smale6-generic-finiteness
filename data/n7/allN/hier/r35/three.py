"""Independent exact enumeration of the 16 origin strata of the n=3 control."""
from itertools import combinations,product
from z3 import Real,RealVal,Solver,And,Or,If,sat,unsat
U=[0,1,30]
es=list(combinations(range(4),2))
def extremum(v,highest):
    best=v[0]
    for x in v[1:]:best=If(x>best if highest else x<best,x,best)
    return best
def tie(v,highest):
    if len(v)<2:return False
    # Every element has at least one different element as good as itself.
    return And([Or([y>=x if highest else y<=x for j,y in enumerate(v) if j!=i]) for i,x in enumerate(v)])
def trial(a,b):
    s=Solver(); s.set(timeout=30000)
    h=[]
    for k,missing in enumerate([a,b]):
        d={e:Real("h%d%d%d"%(k,*e)) for e in es if e!=(missing,3)}
        h.append(d)
        for i,j,l in combinations(range(4),3):
            s.add(tie([d[e] for e in [(i,j),(i,l),(j,l)] if e in d],False))
    z,w=h
    p={e:(z[e]+w[e])/2-U[e[0]]-U[e[1]] if e[1]<3 else -z[e]-w[e]-U[e[0]]
       for e in es if e in z and e in w}
    for own,opp in ((z,w),(w,z)):
        for mask in range(1,8):
            vals=[p[e]+opp[e] if e[1]<3 else -U[e[0]]-own[e] for e in own
                  if bool(mask&(1<<e[0]))!=bool(mask&(1<<e[1]))]
            s.add(tie(vals,True))
    v=extremum(list(p.values()),True)
    s.push();s.add(v==-1); at=s.check();s.pop()
    s.add(v!=-1);other=s.check()
    assert other==unsat
    return at,other
pos=0
for a,b in product([None,0,1,2],repeat=2):
    good,bad=trial(a,b); pos+=good==sat
    print(a,b,"Psi=-1",good,"Psi differs",bad)
assert pos>0
print("positive strata",pos)

