"""Read-only inventory and content audit. Run from r35 with the review environment."""
import collections, gzip, hashlib, json, re, subprocess
from pathlib import Path
from pypdf import PdfReader
from PIL import Image, ImageOps, ImageDraw
import yaml
here=Path(__file__).resolve().parent
src=here.parent/"smale6-generic-finiteness"
dest=here/"pdf"
dest.mkdir(exist_ok=True)
def proc(*argv):
    return subprocess.check_output(argv,cwd=src)
def git(*args):
    return proc("git","--no-optional-locks",*args)
def h(data):
    return hashlib.sha256(data).hexdigest()
manifest={line[66:]:line[:64] for line in (src/"FILES.sha256").read_text().splitlines()}
listed=set(manifest)|{"FILES.sha256"}
status=git("status","--porcelain=v1","-z","--untracked-files=all").decode().split("\0")[:-1]
print("index status",collections.Counter(line[:2] for line in status))
staged={row.split("\t")[1]:row.split()[1] for row in git("ls-files","--stage").decode().splitlines()}
ignored=git("ls-files","--others","--ignored","--exclude-standard").decode()
print("branch",git("symbolic-ref","--short","HEAD").decode().strip(),"remote",git("remote","-v").decode().strip(),"reachable",git("rev-list","--all","--count").decode().strip(),"ignored",repr(ignored))
assert not (set(staged)^listed) and not ignored
print("listed digests",len(manifest),"staged",len(staged))
(here/"files-opened.txt").write_text("\n".join(sorted(listed))+"\n")
print("files by size",sorted(((src/p).stat().st_size,p) for p in listed)[-5:])
print("bytes total",sum((src/p).stat().st_size for p in listed))
pd=src/"paper/alln/main.pdf"
for kind, path in [("release",pd),("rebuilt",here/"tree/paper/alln/main.pdf")]:
    subprocess.run(["pdftotext","-layout",path,dest/(kind+".txt")],check=True)
assert (dest/"release.txt").read_bytes()==(dest/"rebuilt.txt").read_bytes()
pdfmeta=proc("pdfinfo","paper/alln/main.pdf").decode()
print(pdfmeta)
pdf=PdfReader(pd)
named=pdf.named_destinations
bad=[]; actions=collections.Counter()
for page in pdf.pages:
    for ann in page.get("/Annots",[]):
        ann=ann.get_object()
        act=ann.get("/A",{})
        actions[str(act.get("/S",ann.get("/Subtype")))]+=1
        d=act.get("/D",ann.get("/Dest"))
        if isinstance(d,str) and d not in named: bad.append(d)
print("PDF destinations",len(named),"actions",actions,"bad destinations",bad)
assert not bad
subprocess.run(["pdftoppm","-r","95","-png",pd,dest/"page"],check=True)
pages=sorted(dest.glob("page-*.png"))
for i in range(0,len(pages),4):
    sheet=Image.new("RGB",(850,1124),"#dddddd")
    for j,fn in enumerate(pages[i:i+4]):
        im=Image.open(fn).convert("RGB")
        im.thumbnail((416,545))
        x=6+424*(j%2); y=5+560*(j//2)
        sheet.paste(im,(x,y))
        ImageDraw.Draw(sheet).text((x,y+539),str(i+j+1),fill="#333333")
    sheet.save(dest/("sheet-%02d.jpg"%(i+1)),quality=90)

patterns={
"email":r'[\w.+%-]+@[\w.-]+\.[A-Za-z]{2,}',
"machine_path":r'(?:/(?:Users|home|root)/[\w.-]+|[A-Z]:\\Users\\[^\\\s]+|~/[A-Za-z][\w/-]*)',
"temporary_path":r'/(?:tmp|private/var/folders)/[\w./-]+',
"host":r'(?:Linux\s+[a-fA-F0-9]{8,64}\b|(?:hostname|user@|\.internal\b|\.local\b|ssh\s+\w+@)|https?://(?:localhost|127\.0\.0\.1))',
"secret":r'(?:-----BEGIN [\w ]*PRIVATE KEY-----|(?:gh[pousr]_|github_pat_|sk-(?:proj-)?|hf_|AKIA|ASIA|xox[baprs]-|glpat-|AKC)[A-Za-z0-9_-]{12,}|(?:password|api[_ -]?key|access[_ -]?token|secret[_ -]?key)\s*[:=]\s*["\x27]?[A-Za-z0-9_-]{7,})',
"service":r'\b(?:modal(?:\.com|\.run)?|vast\.ai|runpod|together\.ai|lambda\.cloud|openrouter|s3://|wandb(?:\.ai)?|huggingface\.co)\b',
"internal":r'\b(?:TODO|FIXME|HACK|do not (?:publish|release)|internal.only|private (?:repository|repo|server|service)|redact(?:ed|ion)?|redaction)\b',
"machine_id":r'\b(?:cmp_[A-Za-z0-9_-]{12,})',
"ip":r'(?<![\w.])(?:10\.\d{1,3}|192\.168|172\.(?:1[6-9]|2\d|3[01]))(?:\.\d{1,3}){2}(?![\w.])'
}
controls=dict(email="review@example.invalid",machine_path="/Users/test/f",temporary_path="/tmp/test",
    host="Linux deadbeefabcd",secret="ghp_FAKEDETECTIONONLY123",service="runpod",internal="FIXME",
    machine_id="cmp_abcdefghijklm",ip="192.168.1.15")
for k,pat in patterns.items(): assert re.search(pat,controls[k],re.I),k
leanpat=re.compile(r'\b(?:sorry|admit|sorryAx|axiom|unsafe|native_decide|implemented_by)\b')
assert len(leanpat.findall("sorry admit sorryAx axiom unsafe native_decide implemented_by"))==7
hits=collections.defaultdict(list); lean=[]; gz=0; nbytes=0; links=set(); hist_links=[]; pergroup=collections.Counter()
for rel in sorted(listed):
    p=src/rel; raw=p.read_bytes()
    assert rel=="FILES.sha256" or h(raw)==manifest[rel],rel
    assert hashlib.sha1(("blob %d\0"%len(raw)).encode()+raw).hexdigest()==staged[rel],rel
    if p.suffix==".gz":
        raw=gzip.decompress(raw); gz+=1
    if p.suffix==".pdf":
        raw=(pdfmeta+proc("pdfinfo","-meta",str(pd)).decode()+proc("pdfinfo","-custom",str(pd)).decode()+
             (dest/"release.txt").read_text()+proc("pdfinfo","-url",str(pd)).decode()).encode()
    content=raw.decode()
    nbytes+=len(raw)
    if (p.name.endswith((".json",".json.gz"))): json.loads(content)
    if p.name.endswith(".jsonl.gz"):
        for row in content.splitlines(): json.loads(row)
    group=rel.split("/")[4] if rel.startswith("data/n7/allN/hier/") else str(p.relative_to(src).parent)
    pergroup[group]+=1
    checklean=rel.startswith("lean/direct-route/DirectRoute/") or p.name.startswith("Solution") and p.suffix==".lean"
    for n,line in enumerate(content.splitlines(),1):
        for k,pat in patterns.items():
            for x in re.finditer(pat,line,re.I):
                hits[k].append((rel,n,x.group() if k!="secret" else "<candidate requiring inspection>"))
        if checklean and leanpat.search(line): lean.append((rel,n,line.strip()))
    if p.suffix==".md":
        for m in re.finditer(r'\[[^\]\n]*\]\(([^()\s]+)\)',content):
            tgt=m[1]
            if "://" not in tgt and not tgt.startswith(("#","mailto:")) and not (p.parent/tgt.split("#")[0]).exists():
                hist_links.append((rel,content[:m.start()].count("\n")+1,tgt))
    if p.suffix in {".tex",".bib",".md",".cff"} or p.name.startswith("LICENSE"):
        for u in re.findall(r'https?://[^\s<>{}\]\\]+',content):
            u=u.rstrip(".,;:|"); u=u[:-1] if u.count(")")>u.count("(") and u.endswith(")") else u
            if u: links.add(u)
print("all digests and stage blobs matched; areas",dict(pergroup),"gzip members",gz,"scanned content bytes",nbytes)
print("proof token matches",lean)
print("positive control tokens in Challenge:",len(leanpat.findall((src/"lean/direct-route/Challenge.lean").read_text())))
for k in patterns:
    hh=hits[k]
    print(k,"hits",len(hh),"in",len(set(x[0] for x in hh)),"files; distinct",list(dict.fromkeys(x[2] for x in hh))[:24])
(here/"scan-hits.tsv").write_text("".join("%s\t%s\t%d\t%s\n"%(k,p,n,v) for k in hits for p,n,v in hits[k]))
(here/"urls.txt").write_text("\n".join(sorted(links))+"\n")
print("unresolved relative Markdown links",hist_links)
print("CFF",yaml.safe_load((src/"CITATION.cff").read_text()))
print("two licenses",[(p,(src/p).read_text().splitlines()[:2]) for p in ("LICENSE","LICENSE-CC-BY-4.0")])
for v in src.glob("data/n7/allN/hier/*/*/versions.json"):
    tab=json.loads(v.read_text())["sha256"]
    for name,sha in tab.items():
        if v.parent.parent.name=="lean": target=src/"lean/direct-route"/name
        elif name=="nk_fibre.py" and (v.parent/"nk_fibre.as-run.py").exists(): target=v.parent/"nk_fibre.as-run.py"
        else: target=src/"scripts/allN"/name
        if not target.exists(): print("historical version entry only",name); continue
        assert h(target.read_bytes())==sha,(v,name)
print("version hashes verified")
