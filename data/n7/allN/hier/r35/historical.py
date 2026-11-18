"""Replay small historical controls and the documented R30 pickle dependency chain."""
from pathlib import Path
import subprocess,time,os,signal
here=Path(__file__).resolve().parent; tree=here/"tree"; hist=tree/"data/n7/allN/hier"; logs=here/"runs"
py=str(here/"venv/bin/python3"); env=os.environ.copy(); env.update(OMP_NUM_THREADS="1",OPENBLAS_NUM_THREADS="1",PYTHONDONTWRITEBYTECODE="1")
def run(name, where, args, limit):
    before=time.monotonic()
    with (logs/(name+".log")).open("w") as f:
        p=subprocess.Popen([py,*args],cwd=where,stdout=f,stderr=subprocess.STDOUT,env=env,start_new_session=True)
        while p.poll() is None:
            rows=subprocess.check_output(["ps","-axo","pgid=,rss="],text=True).splitlines()
            rss=sum(int(row.split()[1])*1024 for row in rows if row.split()[0]==str(p.pid))
            if rss>3_500_000_000 or time.monotonic()-before>limit:
                os.killpg(p.pid,signal.SIGKILL);break
            time.sleep(.5)
        print(name,p.wait(),round(time.monotonic()-before,2),flush=True)
        return p.returncode
for v in [-40,-20,-1.5,-0.9,0,10,1000]:
    run("n3-"+str(v),tree,["scripts/allN/nk_fibre.py","3","0,1,30","--procs","1","--far-psi="+str(v)],16)
for n in [3,4,5]:run("r30-check2-"+str(n),hist/"r30",["check2.py",str(n)],25)
for name,limit in [("check6fast",250),("lp6",35),("cert6",90),("cert6b",75)]:
    if run("r30-"+name,hist/"r30",[name+".py"],limit):break

