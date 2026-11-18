"""R35. Independent sign-cell decomposition of the real line for Remark 9.1."""
from fractions import Fraction as F
from itertools import combinations, product

# Each pair is (slope, intercept); infinity has its own symbol.
def aff(a, b):
    return (F(a), F(b))

def add(*forms):
    return tuple(map(sum, zip(*forms)))

def scale(a, f):
    return tuple(a*x for x in f)

edges = list(combinations(range(5), 2))
X = aff(1, 0)
z = dict(zip(edges, [aff(-1,-3), aff(2,4), aff(2,4), aff(-1,-2),
                     aff(-1,-3), aff(-1,-3), aff(-1,-3), aff(2,6), aff(-1,-2), aff(-1,-2)]))
w = dict(zip(edges, [aff(0,2), aff(0,0), aff(0,2), aff(0,2),
                     aff(0,0), aff(1,5), aff(1,5), aff(0,0), aff(0,0), None]))
seq = [(0,2),(2,4),(0,4),(0,3)]
expected = set(seq)

def tests(z, w):
    psi = {}
    tests = []
    for d in (z,w):
        for a,b,c in combinations(range(5),3):
            vals = [d[a,b], d[a,c], d[b,c]]
            tests.append(("min", [v for v in vals if v is not None]))
    for e in edges:
        a,b = e
        if b < 4:
            psi[e] = add(scale(F(1,2), add(z[e], w[e])), aff(0,-a-b))
        elif z[e] is not None and w[e] is not None:
            psi[e] = add(scale(-1, add(z[e], w[e])), aff(0,-a))
    for own, other in ((z,w),(w,z)):
        for mask in range(1,16):
            cut = []
            for e in edges:
                a,b = e
                if bool(mask & (1<<a)) == bool(mask & (1<<b)):
                    continue
                if b < 4:
                    cut.append(add(psi[e], other[e]))
                elif own[e] is not None:
                    cut.append(add(aff(0,-a), scale(-1,own[e])))
            tests.append(("cut", cut))
    for e, val in psi.items():
        tests.append(("equal" if e in expected else "less", [val, X]))
    for a,b in ((0,1),(2,3)):
        tests.append(("equal", [w[seq[a]], w[seq[b]]]))
        tests.append(("equal", [z[seq[b]], z[seq[(b+1)%4]]]))
    return tests

def passes(checks, x):
    for kind, forms in checks:
        vals = [a*x+b for a,b in forms]
        if kind in ("min","cut"):
            if not vals or vals.count((min if kind=="min" else max)(vals)) < 2:
                return False
        elif kind == "equal" and vals[0] != vals[1]:
            return False
        elif kind == "less" and not vals[0] < vals[1]:
            return False
    return True

def cells(checks):
    # All pairwise differences in each predicate have constant strict sign between
    # adjacent roots. Endpoints are singleton cells with their own equality tests.
    roots = sorted({(d-b)/(a-c) for _,fs in checks
                    for (a,b),(c,d) in combinations(fs,2) if a != c})
    yield (None,roots[0]), roots[0]-1
    for i,t in enumerate(roots):
        yield (t,t), t
        if i+1 < len(roots):
            yield (t,roots[i+1]), (t+roots[i+1])/2
    yield (roots[-1],None), roots[-1]+1

if __name__ == "__main__":
    checks = tests(z,w)
    print("predicates", len(checks), "triangles",20,"cuts",30)
    for cell, x in cells(checks):
        print(cell, passes(checks,x))
    q=[0]*4
    N=0
    for (a,b),s in zip(seq,(-1,1,-1,1)):
        if b<4:
            N += 3*s
            q[a] += 2*s
            q[b] += 2*s
        else:
            q[a] -= s
    print("N q and dot",N,q,sum(i*v for i,v in enumerate(q)))
    assert (N,q)==(0,[1,0,-3,2])
    assert all(passes(checks,x) for cell,x in cells(checks) if x>3)
    assert passes(checks,F(1000))
    corrupted=w.copy()
    corrupted[1,3]=aff(1,6)
    assert not passes(tests(z,corrupted),F(1000))
    # Examples 3.5/6.4 at (3,4) and 5.4, independently of the released code.
    u0,u1=3,4
    zp=F(0); wp=F(2*u0,3)-zp
    chi=(zp+wp)/2-u0-u1
    assert chi==-zp-wp-u1 and chi-(u1-u0)==-(zp+wp+2*(u1-u0))-u0
    assert -3*chi-2*u0-3*u1==0
    mass=(0,0,1,1); subz={1,2,3}; subw={0,2,3}
    pairs=list(combinations(range(4),2))
    zh={e:2*int(set(e)<=subz) for e in pairs}
    wh={e:2*int(set(e)<=subw) for e in pairs}
    assert all(F(zh[e]+wh[e],2)-sum(mass[i] for i in e)==0 for e in pairs)
    cycle=[(0,1),(1,2),(2,3),(0,3)]
    assert [wh[e] for e in cycle]==[0,0,2,2] and [zh[e] for e in cycle]==[0,2,2,0]
    print("independent controls passed")
