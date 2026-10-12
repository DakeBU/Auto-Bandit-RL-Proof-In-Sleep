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

def real(p):return os.path.normcase(str(Path(p).resolve()))
def family_paths(op):
 op=Path(op);stem=op.name[:-6];bases=[op.parent]
 if '.lake/build/lib/lean' in op.as_posix():bases.append(Path(op.parent.as_posix().replace('/lib/lean','/ir')))
 return sorted({p.resolve() for base in bases for p in base.glob(stem+'.*') if p.is_file()})
def own_family():return [dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in family_paths(P/'StrongConvexAttainmentCanaries.olean')]
def validate_own_family(rows):
 # This direct -o profile permits only the actual main olean. Additional companions reject.
 assert len(rows)==1 and rows[0]['path']==str((P/'StrongConvexAttainmentCanaries.olean').resolve()),'Unexpected own output family'
 assert rows==own_family(),'Own family membership/hash drift'
def check_probe(pins,release,src,mi):
 reviewed=pins['imported_probe']
 assert reviewed==release['recipe']['ImportedAudit-construction-v3.lean'],'Reviewed probe authority differs'
 assert bind(src)==reviewed and mi['probe']==reviewed,'Unreviewed import probe'
def sealed_family_index(sealed):
 index={};parent_keys={}
 for k,row in sealed.items():
  path=Path(row['path']);parent=str(path.parent)
  if parent not in parent_keys:parent_keys[parent]=real(path.parent)
  parent_key=parent_keys[parent];name=path.name
  # Every literal dot prefix exactly matches startswith(stem+'.'), including private companions.
  for i,c in enumerate(name):
   if c=='.':index.setdefault((parent_key,name[:i]),{})[k]=row
 return index

def companion_membership(pins,stage,own=None):
 cl=json.loads((P/'closure-manifest-v3.json').read_text());sealed={real(x['path']):x for x in cl['inputs']}
 assert len(sealed)==len(cl['inputs']),'Duplicate closure paths'
 origins=list(cl['origins'])
 roots=([str(P)] if stage=='import' else [])+pins['scratch_parent_roots']+pins['ordered_search_roots']
 assert len(roots)==len(set(map(real,roots))),'Duplicate effective roots'
 if stage=='import':
  assert own is not None;validate_own_family(own)
  for row in own:sealed[real(row['path'])]=row
  origins.append({'module':'StrongConvexAttainmentCanaries','olean':str(P/'StrongConvexAttainmentCanaries.olean')})
 assert len(origins)==len({x['module'] for x in origins}),'Duplicate expected modules'
 family_index=sealed_family_index(sealed)
 observed=[]
 for row in origins:
  op=Path(row['olean']).resolve();relative=Path(*row['module'].split('.')).with_suffix('.olean')
  hits=[(Path(root)/relative).resolve() for root in roots if (Path(root)/relative).is_file()]
  assert len(hits)==1 and hits[0]==op,'Missing/shadowed/wrong effective module origin: '+row['module']
  stem=op.name[:-6];bases=[op.parent]
  if '.lake/build/lib/lean' in op.as_posix():bases.append(Path(op.parent.as_posix().replace('/lib/lean','/ir')))
  base_keys=set(map(real,bases));expected={}
  for parent_key in base_keys:expected.update(family_index.get((parent_key,stem),{}))
  current=family_paths(op);assert set(map(real,current))==set(expected),'Module companion membership drift: '+row['module']
  current_rows=[bind(p) for p in current]
  assert all(expected[real(x['path'])]==x for x in current_rows),'Module companion hash drift'
  observed.append({'module':row['module'],'olean':str(op),'family':current_rows})
 return observed

def check_prior(rec,stage,source,argv,pins,pinfile,before):
 assert rec['stage']==stage and rec['actual_exit']==0 and rec['integrity_pass'] is True
 assert rec['pre_git']==rec['post_git']==before
 assert rec['argv']==argv and Path(rec['cwd']).resolve()==R
 expected_env={'LEAN_NUM_THREADS':'2','LEAN_PATH':os.pathsep.join(pins['scratch_parent_roots']+pins['ordered_search_roots'])}
 assert rec['env_overrides']==expected_env
 assert rec['before_RAW']==rec['after_RAW']
 assert datetime.datetime.fromisoformat(rec['start_utc']) < datetime.datetime.fromisoformat(rec['end_utc']) <= datetime.datetime.now(datetime.timezone.utc)
 rows=rec['before_RAW'];mapping={os.path.normcase(str(Path(x['path']).resolve())):x for x in rows}
 assert len(rows)==len(mapping)
 for row in [bind(pinfile),bind(source),pins['compiler'],pins['release'],pins['capture'],pins['header_probe']]:
  assert mapping[os.path.normcase(str(Path(row['path']).resolve()))]==row
 assert rec['runtime_before']==rec['runtime_after']==runtime_snapshot(pins)
 for kind in ['stdout','stderr']:assert bind(Path(rec[kind]['path']))==rec[kind]

def exact_frozen_canary_headers(source,frozen):
 parts=re.split(rb'(?m)^theorem ',source);fparts=re.split(rb'(?m)^theorem ',frozen)
 assert len(parts)==len(fparts)==3 and parts[0]==fparts[0]
 ending=b'\nend BanditRL.Tests.OnlineStrongConvexAttainmentCanary\n'
 assert source.endswith(ending) and frozen.endswith(ending)
 for i in [1,2]:
  expected=fparts[i] if i==1 else fparts[i][:-len(ending)]
  assert parts[i].count(b' := by\n')>=1
  assert parts[i].split(b' := by\n',1)[0]==expected.rstrip(b'\n')

FIXED_LINEAGE={'path': 'E:\\ABRL\\worktrees\\research-online-book\\tmp\\online-b4-next-attainment-canary-body-20261012\\import-lineage-fixed-v5.json', 'bytes': 4839, 'sha256': 'a20327201e29f8068f861548f411a6d3a076cc41277155f0cb100010f662b276'}

def probe_output_paths():
 return [P/n for n in ['imported-audit-v1.json','imported-origins-v1.json','provider-operands-v1.txt','positive-TYPE-normalized-v1.txt','positive-VALUE-normalized-v1.txt','zero-TYPE-normalized-v1.txt','zero-VALUE-normalized-v1.txt']]
def require_fresh_probe_outputs():
 paths=probe_output_paths()
 assert all(not os.path.lexists(p) for p in paths),'Probe output already exists; preserve partials and request a separately reviewed namespace'
 return [str(p) for p in paths]

def validate_pin_transport(prior,pins,history):
 expected=dict(prior);expected.update(release=pins['release'],capture=pins['capture'],imported_probe=history['probe_v3'],history=history)
 assert pins==expected,'Unexpected inherited pin delta'
def validate_manifest_transport(oldmi,mi,probe):
 expected=dict(oldmi);expected.update(probe=probe,inputs=[probe])
 assert mi==expected,'Unexpected manifest delta'
def verify_historical_input_maps(receipts):
 allrows={}
 for receipt in receipts:
  rows=receipt['before_RAW'];assert rows==receipt['after_RAW']
  assert len(rows)==len({real(x['path']) for x in rows}),'Duplicate historical input'
  for row in rows:
   k=real(row['path']);assert k not in allrows or allrows[k]==row,'Historical input disagreement'
   assert bind(Path(row['path']))==row,'Historical input drift'
   allrows[k]=row
 return allrows

def validate_observed_diagnostic(diag,failed,before,history):
 assert failed['stage']=='import' and failed['actual_exit']==1 and failed['integrity_pass'] is True
 assert diag['status']=='DIAGNOSTIC_ONLY_NOT_CANARY_ACCEPTANCE' and diag['canary_accepted'] is False
 assert diag['actual_exit']==0 and diag['integrity_pass'] is True and diag['diagnostic_execution_succeeded'] is True
 for obj in [failed,diag]:
  assert obj['pre_git']==obj['post_git']==before
  assert obj['before_RAW']==obj['after_RAW']
  assert obj['runtime_before']==obj['runtime_after'] and len(obj['runtime_before'])==19
  assert obj['companion_membership_before']==obj['companion_membership_after']
 assert failed['runtime_after']==diag['runtime_before'] and failed['companion_membership_after']==diag['companion_membership_before']
 assert datetime.datetime.fromisoformat(failed['end_utc'])<=datetime.datetime.fromisoformat(diag['start_utc'])<datetime.datetime.fromisoformat(diag['end_utc'])<=datetime.datetime.now(datetime.timezone.utc)
 assert diag['stdout']==history['diagnostic_stdout'] and diag['stderr']==history['diagnostic_stderr']
 assert diag['seven_audit_paths_absent_before']==diag['seven_audit_paths_absent_after']==[str(p) for p in probe_output_paths()]

def authenticate_import_lineage(pins,release,before):
 fixed=Path(__file__).resolve().parent/'import-lineage-fixed-v5.json'
 assert bind(fixed)==FIXED_LINEAGE
 history=json.loads(fixed.read_text());assert pins['history']==release['history']==history
 for row in history.values():assert bind(Path(row['path']))==row
 priorfile=Path(history['pins']['path']);prior=json.loads(priorfile.read_text())
 validate_pin_transport(prior,pins,history)
 assert bind(Path(prior['release']['path']))==prior['release'] and bind(Path(prior['capture']['path']))==prior['capture']
 assert prior['capture']==history['capture']
 assert release['independent_tool_review_accepted'] is True
 assert bind(Path(release['independent_tool_review']['path']))==release['independent_tool_review']
 root_return=Path(history['diagnostic_return']['path'])
 assert bind(root_return)==history['diagnostic_return']
 assert release['prior_resource_return']==bind(root_return)
 names=['prepare-import-v5.py','capture-template-import-v5.py','ImportedAudit-construction-v3.lean','import-lineage-fixed-v5.json']
 assert release['recipe']=={n:bind(P/n) for n in names}
 assert pins['capture']==bind(Path(__file__))
 assert Path(__file__).read_bytes()==(P/'capture-template-import-v5.py').read_bytes()
 assert release['scope']=='IMPORTED_ONLY_REUSE_EXACT_PASSED_V3_HEADER_BODY' and release['Lean_resources_released'] is True
 hr=json.loads(Path(history['header']['path']).read_text());br=json.loads(Path(history['body']['path']).read_text())
 cp=Path(history['candidate']['path']);op=P/'StrongConvexAttainmentCanaries.olean'
 check_prior(hr,'header',Path(prior['header_probe']['path']),[prior['compiler']['path'],prior['header_probe']['path']],prior,priorfile,before)
 check_prior(br,'body',cp,[prior['compiler']['path'],'-o',str(op),str(cp)],prior,priorfile,before)
 assert datetime.datetime.fromisoformat(hr['end_utc'])<=datetime.datetime.fromisoformat(br['start_utc'])
 assert hr['companion_membership_before']==hr['companion_membership_after']==br['companion_membership_before']==br['companion_membership_after']
 exact_frozen_canary_headers(cp.read_bytes(),Path(prior['frozen_header']['path']).read_bytes())
 diag=json.loads(Path(history['diagnostic_receipt']['path']).read_text());failed=json.loads(Path(history['failed_import_v2']['path']).read_text())
 validate_observed_diagnostic(diag,failed,before,history)
 assert diag['argv']==[prior['compiler']['path'],history['diagnostic_source']['path']] and Path(diag['cwd']).resolve()==R
 assert failed['argv']==[prior['compiler']['path'],history['probe_v2']['path']] and Path(failed['cwd']).resolve()==R
 expected_env={'LEAN_NUM_THREADS':'2','LEAN_PATH':os.pathsep.join([str(P)]+prior['scratch_parent_roots']+prior['ordered_search_roots'])}
 assert diag['env_overrides']==failed['env_overrides']==expected_env
 allrows=verify_historical_input_maps([hr,br,failed,diag])
 for row in [prior['release'],prior['capture'],history['pins']]:
  assert allrows[real(row['path'])]==row
 assert {real(x['path']):x for x in br['before_RAW']}[real(history['header']['path'])]==history['header']
 paths=[fixed,root_return,Path(release['independent_tool_review']['path']),*[Path(x['path']) for x in history.values()],*[Path(x['path']) for x in allrows.values()]]
 for receipt in [hr,br,failed,diag]:
  for k in ['stdout','stderr']:
   assert bind(Path(receipt[k]['path']))==receipt[k];paths.append(Path(receipt[k]['path']))
 return prior,priorfile,br,paths

ap=argparse.ArgumentParser();ap.add_argument('stage',choices=['import']);ap.add_argument('source');ap.add_argument('attempt');ap.add_argument('--pins-sha256',required=True)
for k in ['header-receipt','header-receipt-sha256','import-manifest','import-manifest-sha256']:ap.add_argument('--'+k)
a=ap.parse_args();pinfile=P/'capture-pins-import-v5.json';assert sha(pinfile)==a.pins_sha256;pins=json.loads(pinfile.read_text());src=safe(a.source);assert src.suffix=='.lean';out=safe(a.attempt);out.mkdir(exist_ok=False)
record=dict(stage=a.stage,status='INCOMPLETE',actual_exit=None,integrity_pass=False);code=1
try:
 own_expected=None
 paths=[pinfile,src];rows=[pins[k] for k in ['python','compiler','operative_search_pins','release','frozen_header','canonical_header','header_probe','freeze','capture']]+pins['parents']+pins['project']
 for row in rows:
  p=Path(row['path']);assert bind(p)==row,'Pinned file drift: '+str(p);paths.append(p)
 assert Path(sys.executable).resolve()==Path(pins['python']['path']).resolve()
 release=json.loads(Path(pins['release']['path']).read_text());assert release['attainment_canary_Lean_authorized'] is True;before=state();assert before==dict(head=release['expected_head'],branch=release['expected_branch'],status='')
 prior_pins,prior_pinfile,prior_body,lineage_paths=authenticate_import_lineage(pins,release,before);paths+=lineage_paths
 frozen=Path(pins['frozen_header']['path']).read_bytes();suffix=b'\n\nend BanditRL.OnlineConvex\n'
 if a.stage=='header':assert bind(src)==pins['header_probe']
 if a.stage in ['header','body','import']:
  cm=P/'closure-manifest-v3.json';assert sha(cm)==pins['closure_manifest_sha256'];paths.append(cm)
  for row in json.loads(cm.read_text())['inputs']:
   pp=Path(row['path']);assert bind(pp)==row;paths.append(pp)
 if a.stage=='body':
  hp=(P/a.header_receipt).resolve();assert hp.is_relative_to(P) and not Path(a.header_receipt).is_absolute();assert sha(hp)==a.header_receipt_sha256;hr=json.loads(hp.read_text());check_prior(hr,'header',Path(pins['header_probe']['path']),[pins['compiler']['path'],pins['header_probe']['path']],pins,pinfile,before);paths.append(hp)
  exact_frozen_canary_headers(src.read_bytes(),frozen)
 if a.stage=='import':
  mp=(P/a.import_manifest).resolve();assert mp.parent==P and not Path(a.import_manifest).is_absolute();assert sha(mp)==a.import_manifest_sha256;mi=json.loads(mp.read_text());paths.append(mp);check_probe(pins,release,src,mi)
  oldmi=json.loads(Path(pins['history']['manifest']['path']).read_text());validate_manifest_transport(oldmi,mi,pins['imported_probe'])
  for row in mi['inputs']:
   p=Path(row['path']);assert bind(p)==row;paths.append(p)
  cp=Path(mi['candidate']['path']);op=Path(mi['olean']['path']);assert cp.parent==P and op.parent==P and op.name=='StrongConvexAttainmentCanaries.olean';assert bind(cp)==mi['candidate'] and bind(op)==mi['olean'];paths += [cp,op]
  rp=Path(mi['receipt']['path']);assert bind(rp)==mi['receipt'];br=json.loads(rp.read_text());assert br==prior_body;check_prior(br,'body',cp,[pins['compiler']['path'],'-o',str(op),str(cp)],prior_pins,prior_pinfile,before);assert br['output_olean']==mi['olean'];assert br['own_family_before']==[];assert mi['output_family']==br['output_family'];own_expected=mi['output_family'];validate_own_family(own_expected);paths += [Path(x['path']) for x in own_expected];paths.append(rp)
 env={k:v for k,v in os.environ.items() if not k.upper().startswith('LEAN_')};env['LEAN_NUM_THREADS']='2';env['LEAN_PATH']=os.pathsep.join(([str(P)] if a.stage=='import' else [])+pins['scratch_parent_roots']+pins['ordered_search_roots'])
 runtime_before=runtime_snapshot(pins);membership_before=companion_membership(pins,a.stage,own_expected)
 argv=[pins['compiler']['path']];target=None
 if a.stage=='body':target=P/'StrongConvexAttainmentCanaries.olean';record['own_family_before']=own_family();assert record['own_family_before']==[],'Own output family must be entirely absent';argv+=['-o',str(target)]
 record['probe_output_paths_absent_before']=require_fresh_probe_outputs()
 argv.append(str(src));paths=list(dict.fromkeys(p.resolve() for p in paths));record.update(runtime_before=runtime_before,companion_membership_before=membership_before,argv=argv,cwd=str(R),env_overrides={k:env[k] for k in ['LEAN_PATH','LEAN_NUM_THREADS']},pre_git=before,before_RAW=[bind(p) for p in paths],start_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());put(out/'pre.json',record)
 with (out/'stdout.raw').open('xb') as stdout,(out/'stderr.raw').open('xb') as stderr:z=subprocess.run(argv,cwd=R,env=env,stdout=stdout,stderr=stderr)
 record.update(actual_exit=z.returncode,end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 CACHE.clear()
 record.update(stdout=bind(out/'stdout.raw'),stderr=bind(out/'stderr.raw'))
 put(out/'child-result.json',{k:record[k] for k in ['actual_exit','end_utc','stdout','stderr']})
 record['probe_outputs_present_after_child']=[bind(p) for p in probe_output_paths() if p.is_file()]
 put(out/'probe-output-result.json',record['probe_outputs_present_after_child'])
 if z.returncode==0:assert len(record['probe_outputs_present_after_child'])==7,'Successful import missing exact output set'
 if a.stage=='body':
  record['output_family']=own_family()
  if z.returncode==0:validate_own_family(record['output_family'])
 runtime_after=runtime_snapshot(pins);membership_after=companion_membership(pins,a.stage,own_expected)
 record.update(runtime_after=runtime_after,companion_membership_after=membership_after,post_git=state(),after_RAW=[bind(p) for p in paths]);record['integrity_pass']=record['pre_git']==record['post_git'] and record['before_RAW']==record['after_RAW'] and runtime_before==runtime_after and membership_before==membership_after
 if a.stage=='body' and z.returncode==0:validate_own_family(record['output_family'])
 if target and target.exists():record['output_olean']=bind(target)
 code=z.returncode or (0 if record['integrity_pass'] else 1);record['status']='ACTUAL_0_INTEGRITY_PASSED' if code==0 else 'FAILED'
except Exception as e:record['error']=str(e)
finally:put(out/'receipt.json',record);print(json.dumps({k:record.get(k) for k in ['status','actual_exit','integrity_pass','error']}))
sys.exit(code)
