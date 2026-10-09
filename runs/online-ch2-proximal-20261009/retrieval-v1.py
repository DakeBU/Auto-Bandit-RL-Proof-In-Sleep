from pathlib import Path
import subprocess,json,hashlib,base64,sys,time
root=Path.cwd();assert root.as_posix()=='E:/ABRL/worktrees/research-online-book'
for v in [1,2]:
    target=root/'tmp'/('online-proximal-APIProbe-v%d.json'%v);assert not target.exists()
    command=['lake','env','lean','tmp/online-proximal-APIProbe-v%d.lean'%v]
    start=time.monotonic();p=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    target.write_bytes((json.dumps(dict(command=command,actual_exit=p.returncode,seconds=time.monotonic()-start,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii'),scope='API-only retrieval, not target body compilation; retain failures.'),indent=2)+'\n').encode('utf8'))
    print(v,p.returncode,p.stdout.decode('utf8',errors='replace'),flush=True)
