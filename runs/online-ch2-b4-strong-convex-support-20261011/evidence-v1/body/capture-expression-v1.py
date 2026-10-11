from pathlib import Path
import json,hashlib,subprocess,sys,datetime
r=Path.cwd();d=r/'tmp/online-b4-support-body-20261011';mode=sys.argv[1]
def bind(p):return {'path':p.relative_to(r).as_posix(),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
def put(n,v):
 with (d/n).open('xb') as f:f.write(v if isinstance(v,bytes) else (json.dumps(v,indent=2)+'\n').encode())
def git(*a):return subprocess.run(['git',*a],check=True,capture_output=True).stdout
module=r/'BanditRLProof/OnlineStrongConvexSupport.lean'; out=r/'.lake/build/lib/lean/BanditRLProof/OnlineStrongConvexSupport.olean'
assert bind(module)['sha256']=='f3a475b58661a4efefdb33b9715852a08008940bd437e1cb3ad64862b772d1e5'
artifacts=lambda:[bind(p) for p in sorted(out.parent.glob('OnlineStrongConvexSupport.*')) if p.is_file()]
if mode=='production-focused-v1':
 assert not artifacts(), 'Existing module build artifacts must not be overwritten'
 argv=['lake','env','lean','-o',out.relative_to(r).as_posix(),module.relative_to(r).as_posix()]
else:argv=['lake','env','lean',(d/sys.argv[2]).relative_to(r).as_posix()]
paths=['BanditRLProof/OnlineStrongConvexSupport.lean','BanditRLProof/OnlineStrongConvexMinimum.lean','BanditRLProof/OnlineClosedProper.lean','BanditRLProof/OnlineConvexExtended.lean','BanditRLProof.lean','Tests.lean','lean-toolchain','lakefile.lean','lake-manifest.json','.lake/build/lib/lean/BanditRLProof/OnlineStrongConvexMinimum.olean','.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Normed/Operator/Basic.olean','docs/contracts/online-ch2-b4-strong-convex-support-v1/neutral-frozen-header-v1.txt']
a={'argv':argv,'cwd':str(r),'head_before':git('rev-parse','HEAD').decode().strip(),'dirty_before_hex':git('status','--porcelain=v1','-z').hex(),'dependencies_before':[bind(r/p) for p in paths],'artifacts_before':artifacts(),'utc_start':datetime.datetime.now(datetime.timezone.utc).isoformat(),'model_request':{'model':'GPT-6 Astra','effort':'medium','runtime_attested':False}}
if mode!='production-focused-v1':a['probe']=bind(d/sys.argv[2])
put(mode+'-pre.json',a);p=subprocess.run(argv,capture_output=True);put(mode+'.stdout.raw',p.stdout);put(mode+'.stderr.raw',p.stderr)
a.update(actual_exit=p.returncode,head_after=git('rev-parse','HEAD').decode().strip(),dirty_after_hex=git('status','--porcelain=v1','-z').hex(),dependencies_after=[bind(r/x) for x in paths],artifacts_after=artifacts(),utc_end=datetime.datetime.now(datetime.timezone.utc).isoformat(),stdout=bind(d/(mode+'.stdout.raw')),stderr=bind(d/(mode+'.stderr.raw')))
a['source_and_existing_binary_bindings_unchanged']=a['dependencies_before']==a['dependencies_after'];put(mode+'-receipt.json',a)
print(json.dumps({'receipt':bind(d/(mode+'-receipt.json')),'actual_exit':p.returncode,'new_artifacts':a['artifacts_after'],'stdout':p.stdout.decode(errors='replace')[:700],'stderr':p.stderr.decode(errors='replace')[:700]},indent=2,ensure_ascii=False))
