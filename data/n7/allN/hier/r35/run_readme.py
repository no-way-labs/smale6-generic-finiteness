"""Run the root README literally, in sequence, in the disposable copy."""
from pathlib import Path
import os, signal, subprocess, time, shutil
base=Path(__file__).resolve().parent
tree=base/"tree"
logs=base/"runs"
logs.mkdir(exist_ok=True)
env=os.environ.copy()
env.update(PATH=str(base/"venv/bin")+":"+env["PATH"], OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1",
           MKL_NUM_THREADS="1", PYTHONDONTWRITEBYTECODE="1", CLANG_MODULE_CACHE_PATH=str(base/"clang-cache"))
readme=(tree/"README.md").read_text().splitlines()
def execute(label, cmd):
    start=time.monotonic()
    peak=0
    with (logs/(label+".log")).open("w") as f:
        proc=subprocess.Popen(["/bin/zsh","-c",cmd],stdout=f,stderr=subprocess.STDOUT,cwd=tree,
                              env=env,start_new_session=True)
        while proc.poll() is None:
            ids=subprocess.check_output(["ps","-axo","pgid=,rss="],text=True)
            rss=sum(int(r.split()[1])*1024 for r in ids.splitlines() if r.split()[0]==str(proc.pid))
            peak=max(peak,rss)
            if rss>=3_500_000_000 or time.monotonic()-start>840:
                os.killpg(proc.pid,signal.SIGKILL)
                break
            time.sleep(.15)
        rc=proc.wait()
    print(label, "rc",rc,"seconds",round(time.monotonic()-start,2),"sampled peak bytes",peak,flush=True)
for lineno, label in [(55,"paper"),(84,"statements"),(92,"cuts"),(97,"cycles-points"),(98,"small"),
                      (119,"exact-r32"),(120,"exact-r33"),(121,"exact-r34"),(122,"remark")]:
    execute(label, readme[lineno-1].strip().split("     #")[0])
execute("trusted","cd lean/direct-route && shasum -a 256 -c TRUSTED.sha256")
for label,ref,trim in [("exact-r32","r32/search_alternating.txt",False),
                       ("exact-r33","r33/check_rank_cycles.txt",False),
                       ("exact-r34","r34/independent_cycles.log",True)]:
    expected=(tree/"data/n7/allN/hier"/ref).read_text().splitlines()
    if trim: expected=expected[:11]
    out=(logs/(label+".log")).read_text().splitlines()
    print(label,"linewise identical",out==expected)

