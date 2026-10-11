from pathlib import Path
import subprocess,os,hashlib,json,datetime,sys
r=Path.cwd();d=r/'tmp/online-b4-vector-adapter-canary-body-20261012';core=r/'tmp/online-b4-vector-adapter-body-20261012';name=sys.argv[1];candidate=d/sys.argv[2];out=d/name;out.mkdir(exist_ok=False)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=[candidate,d/'candidate-v3.lean',d/'VectorAdapterCanaries.olean',core/'candidate-v1.lean',core/'VectorAdapterCandidate.olean',r/'tmp/online-b4-vector-adapter-canary-freeze-20261012/scratch-context-and-statements-frozen-v1.txt',r/'BanditRLProof/OnlineStrongConvexSupport.lean',r/'.lake/build/lib/lean/BanditRLProof/OnlineStrongConvexSupport.olean',r/'BanditRLProof.lean',r/'Tests.lean']
def state():return {'HEAD':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),'status':subprocess.check_output(['git','status','--porcelain=v1']).decode()}
pre=state();before={str(p.relative_to(r)):h(p) for p in paths};start=datetime.datetime.now(datetime.timezone.utc).isoformat()
env=os.environ.copy();env['LEAN_NUM_THREADS']='2';env['LEAN_PATH']=str(d)+os.pathsep+json.loads((core/'imported-audit-v2/receipt.json').read_text(encoding='utf-8'))['env_overrides']['LEAN_PATH']
argv=['C:/Users/admin/.elan/bin/lean.exe',str(candidate)]
z=subprocess.run(argv,cwd=r,env=env,capture_output=True)
(out/'stdout.raw').write_bytes(z.stdout);(out/'stderr.raw').write_bytes(z.stderr);after={str(p.relative_to(r)):h(p) for p in paths}
record={'argv':argv,'cwd':str(r),'env_overrides':{k:env[k] for k in ['LEAN_NUM_THREADS','LEAN_PATH']},'start_utc':start,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actual_exit':z.returncode,'pre_git':pre,'post_git':state(),'before_RAW':before,'after_RAW':after,'inputs_unchanged':before==after,'stdout_sha256':h(out/'stdout.raw'),'stderr_sha256':h(out/'stderr.raw'),'scope':'Ignored experimental scratch canary; no production or acceptance claim'}
if (d/'VectorAdapterCanaries.olean').exists():record['output_olean_sha256']=h(d/'VectorAdapterCanaries.olean')
(out/'receipt.json').write_text(json.dumps(record,indent=2),encoding='utf-8');print('actual_exit='+str(z.returncode));print(z.stdout.decode('utf-8',errors='replace').encode('ascii',errors='backslashreplace').decode());print(z.stderr.decode('utf-8',errors='replace').encode('ascii',errors='backslashreplace').decode())
