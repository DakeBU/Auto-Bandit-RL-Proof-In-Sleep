from pathlib import Path
import argparse,datetime,hashlib,json,os,re,subprocess,sys
if not __debug__: raise SystemExit('Refuse optimized Python: integrity assertions must remain active.')
R=Path('E:/ABRL/worktrees/research-online-book').resolve();D=Path(__file__).resolve().parent
def need(ok,msg):
 if not ok: raise RuntimeError(msg)
def sha(x):
 h=hashlib.sha256()
 with x.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def bind(x):return dict(path=str(x.resolve()),bytes=x.stat().st_size,sha256=sha(x))
def write(x,obj):
 with x.open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
def safe(name,suffix=None):
 need(re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*',name) is not None and name not in ['.','..'],'Unsafe basename')
 x=(D/name).resolve();need(x.parent==D,'Path escape');need(suffix is None or x.suffix==suffix,'Wrong suffix');return x
def trusted(path,digest):
 x=Path(path).resolve();need(x.is_file() and sha(x)==digest,'Trusted input hash mismatch: '+str(x));return x,json.loads(x.read_text(encoding='utf-8'))
def git(*s):return subprocess.check_output(['git','-c','core.longpaths=true',*s],cwd=R).decode().strip()
def state():return dict(head=git('rev-parse','HEAD'),branch=git('branch','--show-current'),status=git('status','--porcelain','--untracked-files=all'))
p=argparse.ArgumentParser()
p.add_argument('stage',choices=['header','body','import']);p.add_argument('source');p.add_argument('receipt_name');p.add_argument('--parent-resource-release',required=True);p.add_argument('--output-module')
for n in ['header-receipt','header-receipt-sha256','import-input-manifest','import-input-manifest-sha256','dependency-receipt','dependency-receipt-sha256']:p.add_argument('--'+n)
a=p.parse_args();need(a.parent_resource_release.strip(),'Explicit parent resource release required')
localpins=D/'capture-pins-v2.json';lp=json.loads(localpins.read_text(encoding='utf-8'))
need(Path(sys.executable).resolve()==Path(lp['python']['path']).resolve(),'Wrong bundled Python executable');need(sha(Path(sys.executable))==lp['python']['sha256'],'Python binary drift')
v6path=Path(lp['operative_v6_pins']['path']);need(sha(v6path)==lp['operative_v6_pins']['sha256'],'V6 pins drift');pins=json.loads(v6path.read_text(encoding='utf-8'))
lean=Path(pins['lean_executable']['path']);need(sha(lean)==pins['lean_executable']['sha256'],'Compiler drift')
authpath=R/'tmp/online-b4-full-iff-freeze-20261012/local-header-freeze-v1.json'
need(sha(authpath)=='17a9695d8328726ea51468b91a101c5e48d8e567e1954a5438b75de0087d9b53','Freeze mismatch');auth=json.loads(authpath.read_text(encoding='utf-8'))
src=safe(a.source,'.lean');need(src.is_file(),'Source absent');out=safe(a.receipt_name);out.mkdir(exist_ok=False)
record=dict(status='INCOMPLETE',actual_exit=None,integrity_pass=False,parent_resource_release=a.parent_resource_release,stage=a.stage)
code=1
try:
 before=state();need(before==dict(head=auth['source_head'],branch=auth['source_branch'],status=''),'Frozen HEAD/branch/clean status mismatch')
 paths=[src,Path(__file__),localpins,v6path,lean,Path(sys.executable),authpath,R/'lean-toolchain',R/'lakefile.lean',R/'lake-manifest.json',R/'BanditRLProof.lean',R/'Tests.lean']
 for x,v in auth['dependency_RAW'].items():
  path=Path(x);need(sha(path)==v,'Frozen dependency drift');paths.append(path)
 for key in ['header','source_pdf','independent_source_review']:
  x=Path(auth[key]['path']);need(sha(x)==auth[key]['sha256'],'Frozen reviewed input drift');paths.append(x)
 for key in ['lean-toolchain','lakefile.lean','lake-manifest.json']:need(sha(R/key)==pins['fixed_pins'][key],'Project pin drift')
 hdr=Path(auth['header']['path']).read_bytes();suffix=b'\n\nend BanditRL.OnlineConvex\n'
 if a.stage=='header':
  expected=hdr.decode().replace('theorem stronglyConvex_iff_sourceSubgradient_growth {E : Type*}','#check ∀ {E : Type*}').replace('(e p)).Nonempty) :','(e p)).Nonempty),').encode()
  need(src.read_bytes()==expected,'Header forall probe differs from frozen transform')
 if a.stage=='body':
  need(a.header_receipt and a.header_receipt_sha256,'Explicit externally pinned successful header receipt required')
  hp,hr=trusted(a.header_receipt,a.header_receipt_sha256);need(hr['stage']=='header' and hr['actual_exit']==0 and hr['integrity_pass'],'Header actual0/integrity missing');paths.append(hp)
  need(src.read_bytes().split(b' := by\n',1)[0]+suffix==hdr,'Frozen body header/context changed')
  for row in hr['before_RAW']:
   x=Path(row['path'])
   if x.name=='HeaderElaboration-v1.lean':need(sha(x)==row['sha256'],'Header probe drift');paths.append(x)
 if a.stage=='import':
  need(a.import_input_manifest and a.import_input_manifest_sha256,'Pinned complete imported probe input manifest required')
  mp,mi=trusted(a.import_input_manifest,a.import_input_manifest_sha256);paths.append(mp)
  need(mi['probe']==bind(src),'Import probe must be authenticated exactly')
  cs=Path(mi['candidate_source']['path']).resolve();co=Path(mi['scratch_olean']['path']).resolve()
  need(cs.parent==D and co.parent==D and co.name=='FullIffCandidate.olean','Wrong scratch source/module binding')
  need(bind(cs)==mi['candidate_source'] and bind(co)==mi['scratch_olean'],'Scratch candidate or olean drift')
  paths.extend([cs,co]);need(cs.read_bytes().split(b' := by\n',1)[0]+suffix==hdr,'Imported candidate header differs')
  for row in mi['all_probe_inputs']:
   x=Path(row['path']).resolve();need(bind(x)==row,'Import probe input mismatch');paths.append(x)
  bp,br=trusted(mi['body_receipt']['path'],mi['body_receipt']['sha256']);need(br['stage']=='body' and br['actual_exit']==0 and br['integrity_pass'],'Scratch BODY receipt invalid');need(br['output_olean']==mi['scratch_olean'],'BODY output is not imported scratch olean');paths.append(bp)
 if a.dependency_receipt:
  need(a.dependency_receipt_sha256,'Dependency receipt hash required');dp,dr=trusted(a.dependency_receipt,a.dependency_receipt_sha256);paths.append(dp);record['dependency_provenance']=bind(dp)
  need(dr.get('actual_exit')==0,'Dependency receipt not actual0')
 olean=R/'.lake/build/lib/lean/BanditRLProof/OnlineStrongConvexSourceSubgradient.olean';need(olean.is_file(),'Canonical adapter olean missing');paths.append(olean)
 roots=[str(Path(x).resolve()) for x in pins['allowed_real_search_roots']]
 need(len(roots)==len(set(x.lower() for x in roots)),'Duplicate pinned roots')
 searchroots=([str(D)] if a.stage=='import' else [])+roots
 env={k:v for k,v in os.environ.items() if not k.upper().startswith('LEAN_')};env['LEAN_NUM_THREADS']='2';env['LEAN_PATH']=os.pathsep.join(searchroots)
 argv=[str(lean)];target=None
 if a.output_module:
  need(a.stage=='body' and a.output_module=='FullIffCandidate','Only actual isolated BODY module output permitted');target=safe(a.output_module+'.olean','.olean');need(not target.exists(),'Output exists');argv+=['-o',str(target)]
 argv.append(str(src));paths=list(dict.fromkeys(x.resolve() for x in paths))
 record.update(argv=argv,cwd=str(R),env_overrides={k:env[k] for k in ['LEAN_PATH','LEAN_NUM_THREADS']},ordered_search_roots=searchroots,pre_git=before,before_RAW=[bind(x) for x in paths],start_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 write(out/'pre.json',record)
 with (out/'stdout.raw').open('xb') as stdout,(out/'stderr.raw').open('xb') as stderr:z=subprocess.run(argv,cwd=R,env=env,stdout=stdout,stderr=stderr)
 record.update(actual_exit=z.returncode,post_git=state(),after_RAW=[bind(x) for x in paths],stdout=bind(out/'stdout.raw'),stderr=bind(out/'stderr.raw'),end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 record['integrity_pass']=record['before_RAW']==record['after_RAW'] and before==record['post_git']
 if target and target.exists():record['output_olean']=bind(target)
 code=z.returncode or (0 if record['integrity_pass'] else 1);record['status']='ACTUAL_0_INTEGRITY_PASSED' if code==0 else 'FAILED'
except Exception as e:record['error']=str(e)
finally:
 write(out/'receipt.json',record)
 print(json.dumps({k:record.get(k) for k in ['status','actual_exit','integrity_pass','error']}))
sys.exit(code)
