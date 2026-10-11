from pathlib import Path
import json,sys,hashlib,subprocess,datetime
r=Path.cwd();d=r/'tmp/online-b4-support-body-20261011'
def bind(p):return {'path':p.relative_to(r).as_posix(),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
def git(*a):return subprocess.run(['git',*a],check=True,capture_output=True).stdout
version=sys.argv[1];candidate=d/(sys.argv[2] if len(sys.argv)>2 else 'Candidate-'+version+'.lean')
def put(n,v):
 with (d/n).open('xb') as f:f.write(v if isinstance(v,bytes) else (json.dumps(v,indent=2)+'\n').encode())
paths=['BanditRLProof/OnlineStrongConvexMinimum.lean','BanditRLProof/OnlineClosedProper.lean','BanditRLProof/OnlineConvexExtended.lean','BanditRLProof.lean','Tests.lean','lean-toolchain','lakefile.lean','lake-manifest.json','.lake/build/lib/lean/BanditRLProof/OnlineStrongConvexMinimum.olean','.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Normed/Operator/Basic.olean','docs/contracts/online-ch2-b4-strong-convex-support-v1/neutral-frozen-header-v1.txt','docs/contracts/online-ch2-b4-strong-convex-support-v1/parent-body-authorization-v1.json']
a={'argv':['lake','env','lean',candidate.relative_to(r).as_posix()],'cwd':str(r),'candidate':bind(candidate),'head_before':git('rev-parse','HEAD').decode().strip(),'dirty_before_hex':git('status','--porcelain=v1','-z').hex(),'dependencies_before':[bind(r/p) for p in paths],'utc_start':datetime.datetime.now(datetime.timezone.utc).isoformat(),'model_request':{'model':'GPT-6 Astra','effort':'medium','runtime_attested':False}}
put(version+'-pre.json',a);p=subprocess.run(a['argv'],capture_output=True);put(version+'.stdout.raw',p.stdout);put(version+'.stderr.raw',p.stderr)
a.update(actual_exit=p.returncode,head_after=git('rev-parse','HEAD').decode().strip(),dirty_after_hex=git('status','--porcelain=v1','-z').hex(),dependencies_after=[bind(r/x) for x in paths],utc_end=datetime.datetime.now(datetime.timezone.utc).isoformat(),stdout=bind(d/(version+'.stdout.raw')),stderr=bind(d/(version+'.stderr.raw')))
a['source_and_binary_bindings_unchanged']=a['dependencies_before']==a['dependencies_after'];put(version+'-receipt.json',a)
print(json.dumps({'receipt':bind(d/(version+'-receipt.json')),'actual_exit':p.returncode,'stdout':p.stdout.decode(errors='replace'),'stderr':p.stderr.decode(errors='replace')},ensure_ascii=False,indent=2))
