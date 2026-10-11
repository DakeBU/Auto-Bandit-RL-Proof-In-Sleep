from pathlib import Path
import subprocess,os,hashlib,json,datetime
r=Path.cwd();d=r/'tmp/online-b4-vector-adapter-alpha-comparator-20261012';core=r/'tmp/online-b4-vector-adapter-body-20261012';canary=r/'tmp/online-b4-vector-adapter-canary-body-20261012'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,v):
 with (d/n).open('x',encoding='utf-8') as f:json.dump(v,f,indent=2)
def state():return {'head':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),'status':subprocess.check_output(['git','status','--porcelain=v1']).decode()}
paths=[d/'CanonicalAlphaProbe-v1.lean',d/'normalizer-fragment-v1.txt',r/'BanditRLProof/OnlineStrongConvexSourceSubgradient.lean',r/'.lake/build/lib/lean/BanditRLProof/OnlineStrongConvexSourceSubgradient.olean',r/'Tests/OnlineStrongConvexSourceSubgradientCanary.lean',r/'.lake/build/lib/lean/Tests/OnlineStrongConvexSourceSubgradientCanary.olean',r/'BanditRLProof/OnlineStrongConvexSupport.lean',r/'.lake/build/lib/lean/BanditRLProof/OnlineStrongConvexSupport.olean',r/'BanditRLProof.lean',r/'Tests.lean',r/'tmp/online-b4-vector-adapter-freeze-20261012/neutral-frozen-header-v1.txt',r/'tmp/online-b4-vector-adapter-canary-freeze-20261012/scratch-context-and-statements-frozen-v1.txt']
env=os.environ.copy();env['LEAN_NUM_THREADS']='2';env['LEAN_PATH']=os.pathsep.join(x for x in json.loads((core/'imported-audit-v2/receipt.json').read_text(encoding='utf-8'))['env_overrides']['LEAN_PATH'].split(os.pathsep) if 'online-b4-vector-adapter' not in x)
record={'argv':['C:/Users/admin/.elan/bin/lean.exe',str(d/'CanonicalAlphaProbe-v1.lean')],'cwd':str(r),'env_overrides':{k:env[k] for k in ['LEAN_NUM_THREADS','LEAN_PATH']},'pre_git':state(),'before_RAW':{str(p.relative_to(r)):h(p) for p in paths},'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
put('canonical-pre-v1.json',record)
z=subprocess.run(record['argv'],cwd=r,env=env,capture_output=True)
(d/'canonical-stdout-v1.raw').write_bytes(z.stdout);(d/'canonical-stderr-v1.raw').write_bytes(z.stderr)
record.update(actual_exit=z.returncode,post_git=state(),after_RAW={str(p.relative_to(r)):h(p) for p in paths},end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),stdout_sha256=h(d/'canonical-stdout-v1.raw'),stderr_sha256=h(d/'canonical-stderr-v1.raw'))
record['inputs_unchanged']=record['before_RAW']==record['after_RAW'];put('canonical-receipt-v1.json',record)
print(json.dumps({'actual_exit':z.returncode,'inputs_unchanged':record['inputs_unchanged'],'stdout':z.stdout.decode('utf-8',errors='replace')[:2500],'stderr':z.stderr.decode('utf-8',errors='replace')[:1000]},ensure_ascii=True))
