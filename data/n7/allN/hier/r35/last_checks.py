"""Read-only close-out checks, including gzip metadata, late-added source and trial diffs."""
from pathlib import Path
import re,gzip,struct,subprocess,json,hashlib
from urllib.parse import urlsplit,urldefrag
base=Path(__file__).resolve().parent;src=base.parent/"smale6-generic-finiteness"
inv=(base/"files-opened.txt").read_text().splitlines()
groups={
"extended-path":r'(?<![\w:])/(?:private/var/folders|Volumes|workspace|mnt)/[\w./-]+|[A-Za-z]:[\\/](?:Users|Documents and Settings)[\\/]\S+',
"provider-or-key":r'\b(?:AKIA[A-Z0-9]{16}|Bearer [A-Za-z0-9_.+/=-]{18,}|eyJ[\w-]{12,}\.[\w-]{10,}\.[\w-]{10,}|sk_live_[A-Za-z0-9]{12,}|-----BEGIN (?:RSA |EC |OPENSSH |DSA )?PRIVATE KEY-----|ssh-(?:rsa|ed25519)\s+[A-Za-z0-9+/=]{28,}|runpod|vast\.ai|modal\.com|ec2-[\w-]+|lambda\.cloud|\.compute\.internal)',
"personal-or-internal":r'\b(?:idiot|incompetent|stupid|embarrass(?:ing|ed)?|off.the.record|secret project|confidential|not for publication|private service|internal note|do not distribute)\b'}
controls=["/private/var/folders/synthetic/path","Bearer SYNTHETIC_ONLY_123456789","off the record"]
for (k,p),v in zip(groups.items(),controls):assert re.search(p,v,re.I)
hits={k:[] for k in groups};urls=set();names=[]
for rel in inv:
    p=src/rel;b=p.read_bytes()
    if p.suffix==".gz":
        flag=b[3];j=10
        if flag & 4:j+=2+int.from_bytes(b[j:j+2],"little")
        if flag&8:
            f=b[j:b.index(b"\0",j)].decode(errors="replace");names.append(f)
        b=gzip.decompress(b)
    if p.suffix==".pdf": b=(base/"pdf/release.txt").read_bytes()
    s=b.decode()
    for i,line in enumerate(s.splitlines(),1):
        for name,expr in groups.items():
            for m in re.finditer(expr,line,re.I):hits[name].append((rel,i,m[0] if name!="provider-or-key" else "format only"))
    if rel not in {"FILES.sha256"}:
        for u in re.findall(r'https?://[^\s<>{}\]\\"]+',s):
            u=u.rstrip(".,;:|*'");u=u[:-1] if u.count(")")>u.count("(") and u.endswith(")") else u
            if u:urls.add(urldefrag(u).url)
print("gzip original filename fields",sorted(set(names)))
print("extended scan",hits)
already={line.split("\t")[0] for line in (base/"links.tsv").read_text().splitlines()[1:]}
extra=sorted(urls-already)
print("additional URL candidates from software, logs and legal texts",extra)
with (base/"extra-links.tsv").open("w") as f:
    for u in extra:
        u=u.rstrip(").") if u.count(")")>u.count("(") else u
        # Only public product/project/documentation hosts seen in the release.
        if urlsplit(u).hostname not in {"github.com","lean-lang.org","leanprover-community.github.io","elan.lean-lang.org","deb.li","creativecommons.org","www.creativecommons.org","arxiv.org","doi.org","www.gnu.org","www.zlib.net","reservoir.lean-lang.org","raw.githubusercontent.com","lakecache.blob.core.windows.net","releases.lean-lang.org"}:
            print("inspect extra manually",u);continue
        p=subprocess.run(["curl","-sSL","-o","/dev/null","--max-time","6","--write-out","%{http_code}",u],capture_output=True)
        f.write(u+"\t"+p.stdout.decode()+"\n")
print("git close",subprocess.check_output(["git","--no-optional-locks","status","--porcelain","--branch"],cwd=src,text=True).splitlines()[0])
for row in (src/"FILES.sha256").read_text().splitlines():
    assert hashlib.sha256((src/row[66:]).read_bytes()).hexdigest()==row[:64]
for suffix in ("A","AB"):
    p=base/("trial-"+suffix)/"paper/alln/main.log";t=p.read_text()
    assert not any(k in t for k in ("Overfull","undefined references","undefined citations","Citation \x60"))
print("verified final source manifest and trial cross-references")

