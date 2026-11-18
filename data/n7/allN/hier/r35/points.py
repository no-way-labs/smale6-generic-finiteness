"""Exact scores of rounded JSON points. All graph edges are inferred from the heights."""
from itertools import combinations
from collections import defaultdict
from decimal import Decimal
from fractions import Fraction as Q
from pathlib import Path
import gzip,json,math
base=Path(__file__).resolve().parent
S=100_000
def scaled(v):
    t=v*S; assert t==int(t)
    return int(t)
def check(u,z,w):
    n=len(u)
    es=list(combinations(range(n+1),2))
    def key(a,b):return (a,b) if a<b else (b,a)
    gap_tri=0
    for d in [z,w]:
        for a,b,c in combinations(range(n+1),3):
            small,second,_=sorted([d[a,b],d[b,c],d[a,c]])
            gap_tri=max(gap_tri,second-small)
    # Scores and cut values are stored in units of 1/(2S).
    s={e:(z[e]+w[e]-2*u[e[0]]-2*u[e[1]] if e[1]<n else -2*(z[e]+w[e]+u[e[0]])) for e in es}
    largest=max(s.values()); gap_cut=0
    for own,opposite in [(z,w),(w,z)]:
        cutval={e:(s[e]+2*opposite[e] if e[1]<n else -2*(u[e[0]]+own[e])) for e in es}
        for mask in range(1,1<<n):
            vals=sorted(v for (a,b),v in cutval.items() if bool(mask&(1<<a))!=bool(mask&(1<<b)))
            gap_cut=max(gap_cut,vals[-1]-vals[-2])
    chosen=[e for e in es if largest-s[e]<2*S//1000]
    adj=defaultdict(list); ends={}
    for e in chosen:
        a,b=e; nodes=[]
        for c,d in enumerate([z,w]):
            cluster=tuple(j for j in range(n+1) if j==a or d[key(a,j)]>=d[e]-S//1000)
            nodes.append((c,cluster))
        ends[e]=tuple(nodes)
        for v in nodes:adj[v].append(e)
    assert adj and all(len(v)==2 for v in adj.values())
    rem=set(chosen); residuals=[]
    while rem:
        edge=min(rem); node=ends[edge][0]; start=node; sign=1; N=0; q=[0]*n
        while edge in rem:
            rem.remove(edge); a,b=edge
            if b==n:q[a]-=sign
            else:N+=3*sign;q[a]+=2*sign;q[b]+=2*sign
            node=next(v for v in ends[edge] if v!=node)
            edge=next(f for f in adj[node] if f!=edge); sign=-sign
        assert node==start and sign==1 and N
        residuals.append(abs(N*largest+2*sum(a*b for a,b in zip(q,u))))
    return largest,gap_cut,gap_tri,residuals,sum(s[e]!=largest for e in chosen)
def heights(p,n,a,b):
    d={tuple(int(x) for x in k):scaled(v) for k,v in p[a].items()}
    d.update({(i,n):scaled(v) for i,v in enumerate(p[b])}); return d
def signature(p):
    return (tuple(sorted(p["zeta"].items())), tuple(p["xi"]),tuple(sorted(p["omega"].items())),tuple(p["eta"]))
if __name__=="__main__":
    ex={(0,1):0,(1,2):0,(0,2):2*S}
    assert check([0,2*S],ex,ex)==(-4*S,0,0,[0],0)
    wrong=ex.copy();wrong[0,1]=S
    try: result=check([0,2*S],wrong,ex)
    except AssertionError:pass
    else:assert result[1]>0 or result[2]>0
    for name in ["HP","GP","WP","BL","BP","AP"]:
        p=next((base/"tree/data/n7/allN/hier/nk").glob("*/"+name+".json.gz"))
        d=json.load(gzip.open(p),parse_float=Decimal);n=d["K"];u=list(map(scaled,d["u"]))
        lines=list(map(lambda x:json.loads(x,parse_float=Decimal),gzip.open(p.with_name(name+".jsonl.gz"))))
        assert len(lines)==len(set(row["iz"] for row in lines))
        flat=[v for l in lines for v in l["found"]]
        assert set(map(signature,flat))==set(map(signature,d["points"]))
        assert sum(l["lps"] for l in lines)==d["lps"] and len(flat)==d["solutions"]
        assert sum(l["odd"] for l in lines)==d["lp_status_other"]==0
        tri=cut=bad=weak=cycles=res=0; mx=None
        bnd=Q((2*n-1)*sum(abs(v) for v in u),3*S)
        for row in d["points"]:
            v,g,t,r,weakmax=check(u,heights(row,n,"zeta","xi"),heights(row,n,"omega","eta"))
            assert g<=2*S//1000 and t<=S//1000 and len(r)==1 and Q(v,2*S)<=bnd
            if d["far"] is not None: assert Q(v,2*S)>=d["far"]
            mx=v if mx is None else max(mx,v)
            tri=max(t,tri);cut=max(g,cut);res=max(res,*r);bad+=g>0;weak+=weakmax>0;cycles+=len(r)
        assert Q(res,2*S)<=Q(2,100000)
        print(name,gzip.open(p.with_name(name+".log.gz"),"rt").readline().strip())
        print(" points",len(d["points"]),"parts",len(lines),"max",Q(mx,2*S),"bound",bnd,
              "maximum cut gap",Q(cut,2*S),"maximum triangle gap",Q(tri,S),"nonexact cuts",bad,
              "tolerance changes E*",weak,"cycles",cycles,"residual",Q(res,2*S))
        ratios=[Q(u[i]-u[i-1],u[i-1]-u[0]) for i in range(2,n)]
        print(" supremum of allowable tau (strict)",min(ratios))

