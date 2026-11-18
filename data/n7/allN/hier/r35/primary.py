"""Download public primary sources needed for numbered citations and record deposited metadata."""
from pathlib import Path
from urllib.parse import quote
import re, subprocess,json
base=Path(__file__).resolve().parent
out=base/"sources"
def curl(url):
    p=subprocess.run(["curl","-sSL","--connect-timeout","4","--max-time","14","--max-filesize","16000000",url],capture_output=True)
    return p.stdout
ids={"smale":"10.1007/BF03025291","moulton":"10.2307/2007159","hampton":"10.1007/s00222-005-0461-0",
"albouy":"10.4007/annals.2012.176.1.10","roberts":"10.1016/S0167-2789(98)00315-7","jensen":"10.56994/JXM.001.002.006",
"changI":"10.1016/j.jsc.2023.102277","changII":"10.1137/24M1716070","diaspan":"10.1007/s10884-019-09765-y",
"mocz19":"10.1007/s10569-019-9920-6","mocz20":"10.1007/s10569-020-09993-1","heintz":"10.1016/0304-3975(83)90002-6",
"heintzerr":"10.1016/0304-3975(85)90150-1","moeckel":"10.1090/S0002-9947-01-02828-8","xia":"10.1016/0022-0396(91)90137-X",
"payne":"10.1007/s00209-008-0374-x","lean":"10.1007/978-3-030-79876-5_37","mathlib":"10.1145/3372885.3373824","highs":"10.1007/s12532-017-0130-5"}
for name,doi in ids.items():
    data=curl("https://api.crossref.org/works/"+quote(doi,safe="/"))
    try:
        d=json.loads(data)["message"]
        print(name, d["title"],d.get("volume"),d.get("issue"),d.get("page",d.get("article-number")),
              d.get("published-print",d.get("published")),[(a.get("given"),a.get("family")) for a in d.get("author",[])])
    except (KeyError,ValueError,TypeError): print(name,"no Crossref metadata")
docs={"tomar6-zenodo":"https://zenodo.org/records/23720035/files/Tomar-Smale6-six-bodies-generic-masses-v5.pdf?download=1",
"tomar6-hexagon":"https://hexagonmath.org/pdf/2611.00377v1","tomar-special":"https://hexagonmath.org/pdf/2611.00485v1",
"nurowski":"https://arxiv.org/pdf/2610.04136","payne-err":"https://web.ma.utexas.edu/users/sampayne/pdf/CorrectionToFibers.pdf",
"poonen":"https://math.mit.edu/~poonen/papers/amsval.pdf","moeckel":"https://www-users.cse.umn.edu/~rmoeckel/research/DziobekAMSLaTeX.pdf",
"chen6":"https://arxiv.org/pdf/2610.23329v1","palmoreII":"https://www.ams.org/journals/bull/1975-81-02/S0002-9904-1975-13794-3/S0002-9904-1975-13794-3.pdf",
"pardo-sebastian":"https://arxiv.org/pdf/2012.15296","payne":"https://arxiv.org/pdf/0705.1732"}
for name,url in docs.items():
    b=curl(url)
    if not b.startswith(b"%PDF"):
        print("no PDF",name,len(b));continue
    p=out/(name+".pdf");p.write_bytes(b)
    subprocess.run(["pdftotext","-layout",p,out/(name+".txt")],check=True)
    print("primary PDF",name,len(b))

