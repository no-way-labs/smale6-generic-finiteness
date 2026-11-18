"""Primary metadata, public URLs in release prose, and Xia full-text discovery."""
from pathlib import Path
import csv, hashlib, html, json, re, subprocess, urllib.parse
import yaml, jsonschema
base=Path(__file__).resolve().parent
tree=base/"tree"; web=base/"sources"; web.mkdir(exist_ok=True)
def fetch(url,seconds=8):
    p=subprocess.run(["curl","-L","-s","-S","--connect-timeout","4","--max-time",str(seconds),
                      "--max-filesize","16000000","--write-out","\nR35HTTP%{http_code}\t%{content_type}\t%{url_effective}",url],
                     capture_output=True,timeout=seconds+3)
    body,_,trace=p.stdout.rpartition(b"\nR35HTTP")
    fields=trace.decode(errors="replace").split("\t")
    status,mime,end=(fields+["","",""])[:3]
    # Avoid forwarding transient download signatures or other query parameters.
    title=""
    if body.startswith(b"%PDF"): title="PDF"
    elif "html" in mime or b"<html" in body[:1000].lower():
        m=re.search(rb"<title\b[^>]*>(.*?)</title>",body,re.I|re.S)
        if m: title=" ".join(html.unescape(m[1].decode(errors="replace")).split())
    return (status,mime,urllib.parse.urlsplit(end).netloc,title[:180],p.returncode),body

extra={
"cff-schema":"https://raw.githubusercontent.com/citation-file-format/citation-file-format/1.2.0/schema.json",
"XiaElsevierPDF":"https://www.sciencedirect.com/science/article/pii/002203969190137X/pdfft?isDTMRedir=true&download=true",
"XiaAuthor":"https://sites.math.northwestern.edu/~xia/",
"XiaOpenAlex":"https://api.openalex.org/works/W1965505736?select=id,open_access,locations,has_content",
"XiaSemantic":"https://api.semanticscholar.org/graph/v1/paper/DOI:10.1016/0022-0396(91)90137-X?fields=title,openAccessPdf,url",
"XiaArchive":"https://archive.org/advancedsearch.php?"+urllib.parse.urlencode({"q":'title:"Central configurations with many small masses" OR (title:"Journal of differential equations" AND year:1991)',"output":"json","rows":50,"fl[]":"identifier"}),
"XiaADS":"https://articles.adsabs.harvard.edu/pdf/1991JDE....91..168X",
"XiaINIST":"https://pascal-francis.inist.fr/vibad/index.php?action=getRecordDetail&idt=5511419",
"HeintzCorrigendum":"https://doi.org/10.1016/0304-3975(85)90150-1",
"OkoloAPI":"https://zenodo.org/api/records/23576138",
"TomarAPI":"https://zenodo.org/api/records/23720035",
}
urls={u.strip().rstrip('"').split("#")[0]:None for u in (base/"urls.txt").read_text().splitlines()}
for k,v in extra.items():urls[v]=k
with (base/"links.tsv").open("w") as f:
    out=csv.writer(f,delimiter="\t")
    out.writerow(["url","status","type","final host","document title","curl exit","size"])
    for url, label in urls.items():
        info,body=fetch(url)
        out.writerow([url,*info,len(body)]);f.flush()
        if label:
            if body.startswith(b"%PDF"): (web/(label+".pdf")).write_bytes(body)
            elif body[:1] in [b"{",b"["]: (web/(label+".json")).write_bytes(body)
            elif label=="XiaAuthor":(web/"XiaAuthor.html").write_bytes(body)
for p in ["XiaOpenAlex","XiaSemantic","XiaArchive"]:
    f=web/(p+".json")
    print(p, f.read_text()[:1550] if f.exists() else "no JSON")
schema=web/"cff-schema.json"
if schema.exists():
    jsonschema.validate(yaml.safe_load((tree/"CITATION.cff").read_text()),json.loads(schema.read_text()))
    print("CITATION.cff valid against official 1.2.0 schema")
books=tree/"paper/alln/references.bib"
for record in re.split(r'(?m)^@',books.read_text())[1:]:
    key=record.split("{",1)[1].split(",")[0]
    if "  journal " not in record and key not in {"wintner1941","lean4","mathlib"}: continue
    def field(name):
        m=re.search(r"(?m)^ *"+name+r"\s*=\s*\{(.+)\}",record)
        return m[1] if m else ""
    title=re.sub("[{}]","",field("title")).replace("$","")
    query=title if key!="ega4iii" else "Éléments de géométrie algébrique IV Étude locale III Grothendieck 1966 IHES 28"
    url="https://api.crossref.org/works?"+urllib.parse.urlencode({"query.bibliographic":query+" "+field("year"),"rows":3})
    info,data=fetch(url,12)
    try: rows=json.loads(data)["message"]["items"]
    except (ValueError,KeyError): print(key,info[:3]);continue
    ref=[(r.get("title"),r.get("DOI"),[(a.get("given"),a.get("family")) for a in r.get("author",[])],
          r.get("volume"),r.get("page") or r.get("article-number"),r.get("published")) for r in rows]
    (web/(key+".json")).write_text(json.dumps(ref,indent=1,ensure_ascii=False))
    print(key,ref[0] if ref else "no records")

