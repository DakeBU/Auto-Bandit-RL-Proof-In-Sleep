from pathlib import Path
import subprocess,json,hashlib,sys,datetime,time
r=Path.cwd();d=r/'tmp/online-ch2-b4-strong-convex-growth-canary-20261011';candidate=d/sys.argv[1];out=d/sys.argv[2];out.mkdir(exist_ok=False)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def gitstate():
 return {k:subprocess.check_output(['git',*v],cwd=r).decode('utf8') for k,v in {'HEAD':['rev-parse','HEAD'],'branch':['branch','--show-current'],'status':['status','--porcelain=v1']}.items()}
bind=[candidate,d/'neutral-consumer-context-v1.txt',d/'neutral-consumer-statements-v1.txt',r/'BanditRLProof/OnlineStrongConvexMinimum.lean',r/'.lake/build/lib/lean/BanditRLProof/OnlineStrongConvexMinimum.olean',r/'docs/contracts/online-ch2-b4-strong-convex-growth-v1/canary-freeze-and-candidate-compile-authorization-v1.json']
pre={str(p.relative_to(r)):h(p) for p in bind};state=gitstate();start=datetime.datetime.now(datetime.timezone.utc).isoformat();argv=['C:/Users/admin/.elan/bin/lake.exe','env','lean',str(candidate.relative_to(r)),'-o',str((out/'Canary.olean').relative_to(r))]
proc=subprocess.run(argv,cwd=r,capture_output=True);end=datetime.datetime.now(datetime.timezone.utc).isoformat();post={str(p.relative_to(r)):h(p) for p in bind};poststate=gitstate()
(out/'stdout.raw').write_bytes(proc.stdout);(out/'stderr.raw').write_bytes(proc.stderr);(out/'candidate.lean.txt').write_bytes(candidate.read_bytes())
receipt={'argv':argv,'cwd':str(r),'start_utc':start,'end_utc':end,'actual_exit':proc.returncode,'pre_git':state,'post_git':poststate,'input_RAW_before':pre,'input_RAW_after':post,'bound_inputs_unchanged':pre==post,'stdout_sha256':h(out/'stdout.raw'),'stderr_sha256':h(out/'stderr.raw'),'clean_claim':False,'failure_class':None if proc.returncode==0 else 'IMPLEMENTATION_FAILED: inspect preserved diagnostics; not source refutation'}
if (out/'Canary.olean').exists():receipt['olean_sha256']=h(out/'Canary.olean')
(out/'receipt.json').write_bytes((json.dumps(receipt,indent=2)+'\n').encode());print(json.dumps({'actual_exit':proc.returncode,'receipt_sha256':h(out/'receipt.json'),'inputs_unchanged':pre==post}));print(proc.stdout.decode('utf8',errors='replace'));print(proc.stderr.decode('utf8',errors='replace'));assert pre==post
