from pathlib import Path
import subprocess,json,hashlib,os,sys,datetime
r=Path.cwd();d=r/'tmp/online-b4-cumulative-producer-canary-body-20261012';name=sys.argv[1];src=d/sys.argv[2];out=d/name;out.mkdir(exist_ok=False)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def bind(p):return {'path':str(p),'sha256':h(p),'bytes':p.stat().st_size}
def state():
 def g(*a):return subprocess.check_output(['git','-c','core.longpaths=true',*a]).decode().strip()
 return {'head':g('rev-parse','HEAD'),'status':g('status','--porcelain=v1')}
authpath=r/'tmp/online-b4-cumulative-producer-canary-freeze-20261012/local-freeze-and-body-authorization-v1.json';auth=json.loads(authpath.read_text(encoding='utf-8'))
assert h(authpath)=='4827f9afb1e04b91ca919d71d0d65ce1d5d63ed16b7fc80d810725f78e7233e7'
for p,v in auth['input_bindings'].items():assert h(r/p)==v,p
paths=[src,authpath,r/'tmp/online-b4-cumulative-producer-canary-freeze-20261012/scratch-context-and-statements-v1.txt',r/'lean-toolchain',r/'lakefile.lean',r/'lake-manifest.json',r/'BanditRLProof.lean',r/'Tests.lean']+[r/p for p in auth['input_bindings']]
for p in ['BanditRLProof/OnlinePrescientBregmanSource.olean','Mathlib/Analysis/Convex/Strong.olean','Mathlib/Algebra/BigOperators/Group/Finset/Basic.olean']:
 x=r/('.lake/packages/mathlib/.lake/build/lib/lean/'+p) if p.startswith('Mathlib') else r/('.lake/build/lib/lean/'+p);paths.append(x)
lean=Path('C:/Users/admin/.elan/toolchains/leanprover--lean4---v4.29.1/bin/lean.exe');paths.append(lean);paths.append(d/'capture-v3.py');paths.append(r/'.lake/build/lib/lean/BanditRLProof/OnlineStrongConvexSupport.olean')
if name.startswith('import'):paths += [d/'candidate-v3.lean',d/'CumulativeProducerCanaries.olean']
env=os.environ.copy()
for k in list(env):
 if k.startswith('LEAN_'):del env[k]
env['LEAN_NUM_THREADS']='2';roots=json.loads((r/'tmp/online-b4-vector-adapter-alpha-comparator-20261012/v4/pins-v4.json').read_text(encoding='utf-8'))['allowed_real_search_roots'];env['LEAN_PATH']=os.pathsep.join(([str(d)] if name.startswith('import') else [])+[str(r/'tmp/online-b4-cumulative-producer-body-20261012')]+roots)
argv=[str(lean)]
if len(sys.argv)>3:
 target=d/sys.argv[3];assert not target.exists();argv+=['-o',str(target)]
argv+=[str(src)]
record={'argv':argv,'cwd':str(r),'env_overrides':{k:env[k] for k in ['LEAN_PATH','LEAN_NUM_THREADS']},'pre_git':state(),'before_RAW':{str(p):h(p) for p in paths},'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};assert record['pre_git']=={'head':auth['source_head'],'status':''}
(out/'pre.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
z=subprocess.run(argv,cwd=r,env=env,capture_output=True);(out/'stdout.raw').write_bytes(z.stdout);(out/'stderr.raw').write_bytes(z.stderr)
record.update(actual_exit=z.returncode,post_git=state(),after_RAW={str(p):h(p) for p in paths},end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),stdout=bind(out/'stdout.raw'),stderr=bind(out/'stderr.raw'))
record['inputs_unchanged']=record['before_RAW']==record['after_RAW']
if len(sys.argv)>3 and target.exists():record['output_olean']=bind(target)
(out/'receipt.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps({'actual_exit':z.returncode,'inputs_unchanged':record['inputs_unchanged'],'stdout':z.stdout.decode('utf-8',errors='replace')[:12000],'stderr':z.stderr.decode('utf-8',errors='replace')[:1500]},ensure_ascii=True));sys.exit(z.returncode if z.returncode else (0 if record['inputs_unchanged'] and record['pre_git']==record['post_git'] else 1))
