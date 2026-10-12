from pathlib import Path
import argparse,json,hashlib,sys,os,subprocess,re,datetime
if not __debug__:raise SystemExit('Refuse optimized Python')
P=Path(__file__).resolve().parent;R=P.parent.parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
CACHE={}
def bind(p):
 p=p.resolve()
 if p not in CACHE:CACHE[p]=dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p))
 return CACHE[p]
def put(p,j):
 with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(j,f,indent=2);f.write('\n')
def safe(name):
 assert re.fullmatch('[A-Za-z0-9][A-Za-z0-9_.-]*',name) and name not in ['.','..'];p=(P/name).resolve();assert p.parent==P;return p
def git(*a):return subprocess.check_output(['git','-c','core.longpaths=true',*a],cwd=R).decode().strip()
def state():return dict(head=git('rev-parse','HEAD'),branch=git('branch','--show-current'),status=git('status','--porcelain','--untracked-files=all'))
def runtime_snapshot(pins):
 row=pins['runtime_inventory'];rp=Path(row['path']);assert bind(rp)==row
 inv=json.loads(rp.read_text());root=Path(inv['toolchain_root'])
 files={p.resolve() for p in (root/'bin').rglob('*') if p.is_file()}
 files |= {p.resolve() for p in (root/'lib').rglob('*') if p.is_file() and p.suffix.lower() in ['.dll','.so','.dylib']}
 expected={str(Path(p).resolve()):h for p,h in inv['files'].items()}
 actual={str(p):sha(p) for p in sorted(files)}
 assert len(actual)==19 and actual==expected,'Portable runtime membership/hash drift'
 return actual

def companion_membership(pins):
 cl=json.loads((P/'closure-manifest-v1.json').read_text());sealed={str(Path(x['path']).resolve()) for x in cl['inputs']}
 actual=set()
 for row in cl['origins']:
  op=Path(row['olean']);stem=op.name[:-6];bases=[op.parent]
  if '.lake/build/lib/lean' in op.as_posix():bases.append(Path(op.parent.as_posix().replace('/lib/lean','/ir')))
  for base in bases:
   actual.update(str(p.resolve()) for p in base.glob(stem+'.*') if p.is_file())
 assert actual <= sealed,'Unsealed current source-library companion'
 return sorted(actual)

ap=argparse.ArgumentParser();ap.add_argument('stage',choices=['header','body','import']);ap.add_argument('source');ap.add_argument('attempt');ap.add_argument('--pins-sha256',required=True)
for k in ['header-receipt','header-receipt-sha256','import-manifest','import-manifest-sha256']:ap.add_argument('--'+k)
a=ap.parse_args();pinfile=P/'capture-pins-v2.json';assert sha(pinfile)==a.pins_sha256;pins=json.loads(pinfile.read_text());src=safe(a.source);assert src.suffix=='.lean';out=safe(a.attempt);out.mkdir(exist_ok=False)
record=dict(stage=a.stage,status='INCOMPLETE',actual_exit=None,integrity_pass=False);code=1
try:
 paths=[pinfile,src];rows=[pins[k] for k in ['python','compiler','operative_search_pins','release','frozen_header','canonical_header','header_probe','freeze','capture']]+pins['parents']+pins['project']
 for row in rows:
  p=Path(row['path']);assert bind(p)==row,'Pinned file drift: '+str(p);paths.append(p)
 assert Path(sys.executable).resolve()==Path(pins['python']['path']).resolve()
 release=json.loads(Path(pins['release']['path']).read_text());before=state();assert before==dict(head=release['expected_head'],branch=release['expected_branch'],status='')
 frozen=Path(pins['frozen_header']['path']).read_bytes();suffix=b'\n\nend BanditRL.OnlineConvex\n'
 if a.stage=='header':assert bind(src)==pins['header_probe']
 if a.stage in ['header','body','import']:
  cm=P/'closure-manifest-v1.json';assert sha(cm)==pins['closure_manifest_sha256'];paths.append(cm)
  for row in json.loads(cm.read_text())['inputs']:
   pp=Path(row['path']);assert bind(pp)==row;paths.append(pp)
 if a.stage=='body':
  hp=(P/a.header_receipt).resolve();assert hp.is_relative_to(P) and not Path(a.header_receipt).is_absolute();assert sha(hp)==a.header_receipt_sha256;hr=json.loads(hp.read_text());assert hr['stage']=='header' and hr['actual_exit']==0 and hr['integrity_pass'];paths.append(hp)
  assert src.read_bytes().split(b' := by\n',1)[0]+b'\n\nend BanditRL.Tests.OnlineWeierstrassExtendedCanary\n'==frozen
 if a.stage=='import':
  mp=(P/a.import_manifest).resolve();assert mp.parent==P and not Path(a.import_manifest).is_absolute();assert sha(mp)==a.import_manifest_sha256;mi=json.loads(mp.read_text());paths.append(mp);assert mi['probe']==bind(src)
  for row in mi['inputs']:
   p=Path(row['path']);assert bind(p)==row;paths.append(p)
  cp=Path(mi['candidate']['path']);op=Path(mi['olean']['path']);assert cp.parent==P and op.parent==P and op.name=='WeierstrassExtendedCanary.olean';assert bind(cp)==mi['candidate'] and bind(op)==mi['olean'];paths += [cp,op]
  rp=Path(mi['receipt']['path']);assert bind(rp)==mi['receipt'];br=json.loads(rp.read_text());assert br['actual_exit']==0 and br['integrity_pass'] and br['output_olean']==mi['olean'];paths.append(rp)
 env={k:v for k,v in os.environ.items() if not k.upper().startswith('LEAN_')};env['LEAN_NUM_THREADS']='2';env['LEAN_PATH']=os.pathsep.join(([str(P)] if a.stage=='import' else [])+pins['scratch_parent_roots']+pins['ordered_search_roots'])
 runtime_before=runtime_snapshot(pins);membership_before=companion_membership(pins)
 argv=[pins['compiler']['path']];target=None
 if a.stage=='body':target=P/'WeierstrassExtendedCanary.olean';assert not target.exists();argv+=['-o',str(target)]
 argv.append(str(src));paths=list(dict.fromkeys(p.resolve() for p in paths));record.update(runtime_before=runtime_before,companion_membership_before=membership_before,argv=argv,cwd=str(R),env_overrides={k:env[k] for k in ['LEAN_PATH','LEAN_NUM_THREADS']},pre_git=before,before_RAW=[bind(p) for p in paths],start_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());put(out/'pre.json',record)
 with (out/'stdout.raw').open('xb') as stdout,(out/'stderr.raw').open('xb') as stderr:z=subprocess.run(argv,cwd=R,env=env,stdout=stdout,stderr=stderr)
 CACHE.clear()
 runtime_after=runtime_snapshot(pins);membership_after=companion_membership(pins)
 record.update(runtime_after=runtime_after,companion_membership_after=membership_after,actual_exit=z.returncode,post_git=state(),after_RAW=[bind(p) for p in paths],stdout=bind(out/'stdout.raw'),stderr=bind(out/'stderr.raw'),end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());record['integrity_pass']=record['pre_git']==record['post_git'] and record['before_RAW']==record['after_RAW'] and runtime_before==runtime_after and membership_before==membership_after
 if target and target.exists():record['output_olean']=bind(target)
 code=z.returncode or (0 if record['integrity_pass'] else 1);record['status']='ACTUAL_0_INTEGRITY_PASSED' if code==0 else 'FAILED'
except Exception as e:record['error']=str(e)
finally:put(out/'receipt.json',record);print(json.dumps({k:record.get(k) for k in ['status','actual_exit','integrity_pass','error']}))
sys.exit(code)
