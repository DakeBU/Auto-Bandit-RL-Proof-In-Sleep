from pathlib import Path
import argparse,datetime,hashlib,json,os,subprocess,sys
R=Path('E:/ABRL/worktrees/research-online-book');D=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('stage',choices=['header','body','import']);p.add_argument('source');p.add_argument('receipt_name');p.add_argument('--parent-resource-release',required=True);p.add_argument('--output-module');a=p.parse_args()
if not a.parent_resource_release.strip():raise SystemExit('Explicit parent resource-release evidence is required.')
def sha(x):return hashlib.sha256(x.read_bytes()).hexdigest()
def bind(x):return dict(path=str(x),bytes=x.stat().st_size,sha256=sha(x))
def git(*s):return subprocess.check_output(['git','-c','core.longpaths=true',*s],cwd=R).decode().strip()
def state():return dict(head=git('rev-parse','HEAD'),branch=git('branch','--show-current'),status=git('status','--porcelain'))
authpath=R/'tmp/online-b4-full-iff-freeze-20261012/local-header-freeze-v1.json'
assert sha(authpath)=='17a9695d8328726ea51468b91a101c5e48d8e567e1954a5438b75de0087d9b53'
auth=json.loads(authpath.read_text(encoding='utf-8'));src=D/a.source;assert src.parent==D and src.is_file()
before=state();assert before==dict(head=auth['source_head'],branch=auth['source_branch'],status='')
for x,v in auth['dependency_RAW'].items():assert sha(Path(x))==v
for key in ['header','source_pdf','independent_source_review']:assert sha(Path(auth[key]['path']))==auth[key]['sha256']
out=D/a.receipt_name;assert out.parent==D;out.mkdir(exist_ok=False)
if a.stage=='body':
 prior=json.loads((D/'header-v1/receipt.json').read_text(encoding='utf-8'));assert prior['actual_exit']==0 and prior['integrity_pass']
 h=Path(auth['header']['path']).read_bytes();b=src.read_bytes();assert b.split(b' := by\n',1)[0]+b'\n\nend BanditRL.OnlineConvex\n'==h
lean=Path('C:/Users/admin/.elan/toolchains/leanprover--lean4---v4.29.1/bin/lean.exe')
pins=R/'tmp/online-b4-vector-adapter-alpha-comparator-20261012/v4/pins-v4.json'
roots=json.loads(pins.read_text(encoding='utf-8'))['allowed_real_search_roots']
env={k:v for k,v in os.environ.items() if not k.startswith('LEAN_')};env['LEAN_NUM_THREADS']='2';env['LEAN_PATH']=os.pathsep.join(([str(D)] if a.stage=='import' else [])+roots)
paths=[src,Path(__file__),authpath,Path(auth['header']['path']),Path(auth['independent_source_review']['path']),pins,lean,R/'lean-toolchain',R/'lakefile.lean',R/'lake-manifest.json',R/'BanditRLProof.lean',R/'Tests.lean']+[Path(x) for x in auth['dependency_RAW']]
olean=R/'.lake/build/lib/lean/BanditRLProof/OnlineStrongConvexSourceSubgradient.olean';assert olean.exists();paths.append(olean)
argv=[str(lean)];target=None
if a.output_module:
 assert a.output_module.isidentifier();target=D/(a.output_module+'.olean');assert not target.exists();argv+=['-o',str(target)]
argv.append(str(src));record=dict(argv=argv,cwd=str(R),env_overrides={k:env[k] for k in ['LEAN_PATH','LEAN_NUM_THREADS']},parent_resource_release=a.parent_resource_release,pre_git=before,before_RAW=[bind(x) for x in paths],start_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(out/'pre.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
z=subprocess.run(argv,cwd=R,env=env,capture_output=True);(out/'stdout.raw').write_bytes(z.stdout);(out/'stderr.raw').write_bytes(z.stderr)
record.update(actual_exit=z.returncode,post_git=state(),after_RAW=[bind(x) for x in paths],stdout=bind(out/'stdout.raw'),stderr=bind(out/'stderr.raw'),end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
record['integrity_pass']=record['before_RAW']==record['after_RAW'] and before==record['post_git']
if target and target.exists():record['output_olean']=bind(target)
(out/'receipt.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps(dict(actual_exit=z.returncode,integrity_pass=record['integrity_pass'],stdout=z.stdout.decode('utf-8',errors='replace')[:9000],stderr=z.stderr.decode('utf-8',errors='replace')[:2000])))
sys.exit(z.returncode or (0 if record['integrity_pass'] else 1))
