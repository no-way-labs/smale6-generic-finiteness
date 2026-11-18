"""Transport the independent census to R30's pickle format, then run its archived checks unchanged."""
from pathlib import Path
from itertools import combinations
import os, subprocess, pickle, sys
base=Path(__file__).resolve().parent
hist=base/"tree/data/n7/allN/hier/r30"
sys.path.insert(0,str(hist))
from check_cycles import hierarchies, node_map, simple_cycles, qvec
s=(base/"count.cpp").read_text()
anchor="++stats.feasible;"
assert s.count(anchor)==1
extra="""if(nodes && n==6) {
            printf("WITNESS %d",plus|minus);
            for(int j=0;j<edges;++j) printf(" %d",z.cluster[j]);
            for(int j=0;j<edges;++j) printf(" %d",w.cluster[j]);
            puts("");
        }"""
source=base/"count_witnesses.cpp";source.write_text(s.replace(anchor,anchor+"\n        "+extra))
subprocess.run(["clang++","-O3","-std=c++17","-o",base/"count_witnesses",source],check=True,timeout=30)
record=subprocess.check_output([base/"count_witnesses"],text=True,timeout=45);(base/"witnesses.log").write_text(record)
hs=list(hierarchies(range(6)))
p=list(combinations(range(6),2))
def key(h):
    return tuple(min(sum(1<<i for i in c) for c in h if {a,b}<=c) for a,b in p)
idx={key(h):i for i,h in enumerate(hs)}
assert len(idx)==2752
surv=set()
for line in record.splitlines():
    if not line.startswith("WITNESS "):continue
    bits,*labels=map(int,line.split()[1:])
    z=idx[tuple(labels[:15])];w=idx[tuple(labels[15:])]
    for l,r in ((z,w),(w,z)):
        zl,cl=node_map(hs[l],6);wr,cr=node_map(hs[r],6)
        cycles=[c for c in simple_cycles([(zl[e],wr[e]) for e in p],len(cl),len(cr))
                if sum(1<<i for i in c)==bits and not any(qvec(c,p,6,1))]
        assert len(cycles)==1
        surv.add((l,r,tuple(cycles[0])))
assert len(surv)==192
with (hist/"surv6.pkl").open("wb") as f:pickle.dump((hs,sorted(surv)),f)
print("192 ordered independent witnesses decoded and checked with archived node and cycle functions")
for name in ["lp6","cert6","cert6b"]:
    with (base/"runs"/("recovered-r30-"+name+".log")).open("w") as f:
        p=subprocess.run([sys.executable,name+".py"],cwd=hist,stdout=f,stderr=subprocess.STDOUT,timeout=90,
                         env=dict(os.environ,OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1"))
    print(name,"return",p.returncode,flush=True)
    assert p.returncode==0

