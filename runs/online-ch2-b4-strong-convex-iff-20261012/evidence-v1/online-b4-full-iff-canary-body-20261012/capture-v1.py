from pathlib import Path
import sys,os,json,hashlib,subprocess,re,datetime
if not __debug__:raise SystemExit('Optimized Python prohibited')
R=Path('E:/ABRL/worktrees/research-online-book');D=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def rec(p):return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=sha(p))
def put(p,j):
 with p.open('x',encoding='utf-8') as f:json.dump(j,f,indent=2)
def git(*a):return subprocess.check_output(['git','-c','core.longpaths=true',*a],cwd=R).decode().strip()
def state():return [git('rev-parse','HEAD'),git('branch','--show-current'),git('status','--porcelain','--untracked-files=all')]
attempt,source=sys.argv[1:3]
for x in [attempt,source]:assert re.fullmatch('[A-Za-z0-9_.-]+',x) and x not in ['.','..']
out=D/attempt;out.mkdir(exist_ok=False);src=D/source
authpath=R/'tmp/online-b4-full-iff-canary-freeze-20261012/local-freeze-and-body-authorization-v1.json';assert sha(authpath)=='05f6a8ae3cc093e8576e45c1ff65cecfe6802d8c52e2d781010bbf652f0c3ac9';auth=json.loads(authpath.read_text())
pinsPath=R/'tmp/online-b4-full-iff-body-20261012/capture-pins-v2.json';pins=json.loads(pinsPath.read_text());assert Path(sys.executable).resolve()==Path(pins['python']['path']).resolve() and sha(Path(sys.executable))==pins['python']['sha256']
v6=Path(pins['operative_v6_pins']['path']);assert sha(v6)==pins['operative_v6_pins']['sha256'];v=json.loads(v6.read_text());lean=Path(v['lean_executable']['path']);assert sha(lean)==v['lean_executable']['sha256']
paths=[src,Path(__file__),authpath,pinsPath,v6,lean,Path(sys.executable),R/'lean-toolchain',R/'lake-manifest.json',R/'lakefile.lean',R/'BanditRLProof.lean',R/'Tests.lean']
for key,value in auth.items():
 if isinstance(value,dict) and 'path' in value and 'sha256' in value:
  p=Path(value['path']);assert sha(p)==value['sha256'];paths.append(p)
for row in auth['headers']+auth['neutral_outputs']:
 p=Path(row['path']);assert sha(p)==row['sha256'];paths.append(p)
if attempt.startswith('focused'):
 hr=json.loads((D/'header-v1/receipt.json').read_text());assert hr['actual_exit']==0 and hr['integrity_pass'];paths.append(D/'header-v1/receipt.json')
 text=src.read_text(encoding='utf-8');ctx=Path(auth['scratch_context']['path']).read_text(encoding='utf-8')
 prefix=ctx.split('theorem box_converse_originalNorm')[0];suffix='\nend BanditRL.Tests.OnlineStrongConvexSubgradientIffCanary\n'
 h1=Path(auth['headers'][0]['path']).read_text(encoding='utf-8');h2=Path(auth['headers'][1]['path']).read_text(encoding='utf-8')
 assert text.startswith(prefix+h1.rstrip('\n')+' := by\n')
 assert text.split('theorem absent_support_vacuity',1)[1].startswith(h2.split('theorem absent_support_vacuity',1)[1].rstrip('\n')+' := by\n')
 assert text.endswith(suffix)
if attempt.startswith('import'):
 paths.extend([D/'FullIffCanaries.olean',D/sys.argv[3]])
env={k:v for k,v in os.environ.items() if not k.upper().startswith('LEAN_')};env['LEAN_NUM_THREADS']='2';env['LEAN_PATH']=os.pathsep.join(([str(D)] if attempt.startswith('import') else [])+[str(R/'tmp/online-b4-full-iff-body-20261012')]+v['allowed_real_search_roots'])
argv=[str(lean)];target=None
if attempt.startswith('focused'):
 target=D/'FullIffCanaries.olean';assert not target.exists();argv+=['-o',str(target)]
argv.append(str(src));before=state();assert before==[auth['source_head'],auth['source_branch'],'']
record=dict(argv=argv,cwd=str(R),env_overrides={k:env[k] for k in ['LEAN_PATH','LEAN_NUM_THREADS']},pre_git=before,before_RAW=[rec(p) for p in paths],start_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
put(out/'pre.json',record)
with (out/'stdout.raw').open('xb') as stdout,(out/'stderr.raw').open('xb') as stderr:z=subprocess.run(argv,cwd=R,env=env,stdout=stdout,stderr=stderr)
record.update(actual_exit=z.returncode,post_git=state(),after_RAW=[rec(p) for p in paths],stdout=rec(out/'stdout.raw'),stderr=rec(out/'stderr.raw'));record['integrity_pass']=record['pre_git']==record['post_git'] and record['before_RAW']==record['after_RAW']
if target and target.exists():record['output_olean']=rec(target)
put(out/'receipt.json',record);print(json.dumps(dict(actual_exit=z.returncode,integrity_pass=record['integrity_pass'])));sys.exit(z.returncode or (0 if record['integrity_pass'] else 1))
