import argparse, subprocess, hashlib, json, datetime
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--label',required=True);p.add_argument('command',nargs=argparse.REMAINDER);a=p.parse_args()
r=Path('E:/ABRL/worktrees/research-online-book');d=r/'tmp/online-ch2-b4-finite-identity-delivery-20261011'/a.label
if d.exists():raise ValueError('create-only output')
d.mkdir();argv=a.command[1:] if a.command[:1]==['--'] else a.command
def sha(b):return hashlib.sha256(b).hexdigest()
def state():return {'HEAD':subprocess.check_output(['git','rev-parse','HEAD'],cwd=r).decode().strip(),'status_hex':subprocess.check_output(['git','status','--porcelain=v1','-z'],cwd=r).hex()}
pre=state();start=datetime.datetime.now(datetime.timezone.utc).isoformat();v=subprocess.run(argv,cwd=r,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
(d/'stdout.raw').write_bytes(v.stdout);(d/'stderr.raw').write_bytes(v.stderr)
rec={'argv':argv,'cwd':str(r),'start_utc':start,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actual_exit':v.returncode,'pre_git':pre,'post_git':state(),'stdout_sha256':sha(v.stdout),'stderr_sha256':sha(v.stderr),'capture_helper_sha256':sha(Path(__file__).read_bytes())}
(d/'receipt.json').write_bytes((json.dumps(rec,indent=2)+'\n').encode());print(json.dumps({'receipt':str(d/'receipt.json'),'actual_exit':v.returncode,'stdout_preview':v.stdout.decode(errors='replace')[:800],'stderr_preview':v.stderr.decode(errors='replace')[:800]}));raise SystemExit(v.returncode)
