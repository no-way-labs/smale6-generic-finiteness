from pathlib import Path
import csv,gzip,hashlib,json,os,re,subprocess
from itertools import combinations
import yaml,jsonschema
base=Path(__file__).resolve().parent; tree=base/"tree"
project=tree/"lean/direct-route"
paper=(tree/"paper/alln/main.tex").read_text()
maps=(project/"README.md").read_text()
for suffix in ["","A","B"]:
    conf=json.loads((project/("comparator"+suffix+".json")).read_text())
    f=project/(conf["challenge_module"]+".lean"); names=re.findall(r'(?m)^theorem (\w+)',f.read_text())
    assert names==conf["theorem_names"] and conf["permitted_axioms"]==["propext","Quot.sound","Classical.choice"]
    history=next((tree/"data/n7/allN/hier/lean").glob("*/comparator"+suffix+".nosandbox.log.gz"))
    lines=gzip.open(history,"rt").read().splitlines()
    print(f.name,len(f.read_text().splitlines()),names,"Table 4 or supplementary examples:",[(name,name in paper) for name in names if name not in paper])
    assert all(name in maps for name in names)
    print(history.name,[line.strip() for line in lines if 'accepts the solution' in line],lines[-1])
for kind in ["paper","references"]:
    a=tree/"docs/as-read"/("R34-"+kind+(".tex" if kind=="paper" else ".bib"))
    b=tree/"paper/alln"/("main.tex" if kind=="paper" else "references.bib")
    dif=subprocess.run(["diff","-U0",a,b],capture_output=True,text=True)
    (base/("R34-"+kind+".diff")).write_text(dif.stdout)
    print(kind,[x.split("@@")[1].strip() for x in dif.stdout.splitlines() if x.startswith("@@")])
bib=(tree/"paper/alln/references.bib").read_text()
bibkeys=set(re.findall(r'@\w+\{([^,]+),',bib))
cited={k for match in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',paper) for k in match.split(",")}
print("bib entries",len(bibkeys),"cited",len(cited),"unused",bibkeys-cited,"unresolved",cited-bibkeys)
assert not (cited-bibkeys) and not re.search(r'\\(?:eq)?ref\{_deliberate_missing_',paper)
strings=set(re.findall(r'\\label\{([^}]+)\}',paper))
refs=set(re.findall(r'\\(?:eq)?ref\{([^}]+)\}',paper))
assert not (refs-strings) and "_deliberate_missing_" not in strings
print("source refs",len(refs),"labels",len(strings))
C=yaml.safe_load((tree/"CITATION.cff").read_text());C["license"]=["MIT","CC-BY-4.0"]
jsonschema.validate(C,json.loads((base/"sources/cff-schema.json").read_text()))
print("suggested CFF licenses valid")
# Opaque historical job IDs in names and content, with a control that uses the actual filename delimiters.
mp=re.compile(r'cmp_[A-Za-z0-9_-]{16,}')
assert mp.search("fake_cmp_0123456789abcdef")
print("job IDs in path components",sorted({m[0] for p in (base/"files-opened.txt").read_text().splitlines() for m in mp.finditer(p)}))
for p in tree.glob("docs/**/*.md"):
    last=0;fence=False
    for i,line in enumerate(p.read_text().splitlines(),1):
        if line.startswith(chr(96)*3): fence=not fence
        if fence or not line.startswith("|"):last=0;continue
        cols=len(re.findall(r'(?<!\\)\|',line))-1
        if last and cols!=last: print("GFM delimiter count",p.relative_to(tree),i,last,cols)
        last=last or cols
for line in (tree/"docs/allN-direct-route-lean-review-3.md").read_text().splitlines():
    for n in re.findall(r'main\.tex#L(\d+)',line):
        tag=(tree/"docs/as-read/R33-paper.tex").read_text().splitlines()[int(n)-1].strip()[:100]
        print("old line",n,tag)
# Check the four generated files and their definition extract in the throwaway copy only.
for name in ["degree","lemmaA","alt"]:
    subprocess.run(["python3","scripts/allN/lean_gen_"+name+".py"],cwd=tree,check=True)
orig=base.parent/"smale6-generic-finiteness"
for f in (project/"DirectRoute").glob("*.lean"):
    assert f.read_bytes()==(orig/f.relative_to(tree)).read_bytes(),f
print("all generated Lean files byte-identical to release")
print("R30 recipe dependencies")
for name in ["check2","check6fast","lp6","cert6","cert6b","d4n4","d4n4b","run6","n7rand"]:
    f=tree/"data/n7/allN/hier/r30"/(name+".py")
    print(name,re.findall(r'open\(["\x27]([^"\x27]+)',f.read_text()))

