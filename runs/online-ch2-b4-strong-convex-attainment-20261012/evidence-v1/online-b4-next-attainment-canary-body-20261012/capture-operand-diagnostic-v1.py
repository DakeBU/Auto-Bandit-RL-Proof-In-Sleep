"""One stdout-only read-only diagnostic; never a canary acceptance recipe."""
from pathlib import Path
import argparse,ast,datetime,hashlib,json,os,subprocess,sys
if not __debug__:raise RuntimeError('Optimized Python forbidden')
P=Path(__file__).resolve().parent;R=P.parent.parent
def raw_sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def read(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def assert_failed_observation(rec,expected):
 assert rec['stage']=='import' and rec['actual_exit']==1 and rec['integrity_pass'] is True
 assert rec['pre_git']==rec['post_git']==expected
 assert rec['before_RAW']==rec['after_RAW']
 assert rec['runtime_before']==rec['runtime_after'] and len(rec['runtime_before'])==19
 assert rec['companion_membership_before']==rec['companion_membership_after']
 assert datetime.datetime.fromisoformat(rec['start_utc'])<datetime.datetime.fromisoformat(rec['end_utc'])<=datetime.datetime.now(datetime.timezone.utc)
def diagnostic_outcome(child_exit,integrity):
 return dict(status='DIAGNOSTIC_ONLY_NOT_CANARY_ACCEPTANCE',actual_exit=child_exit,integrity_pass=integrity,diagnostic_execution_succeeded=child_exit==0 and integrity,canary_accepted=False)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--release',required=True);ap.add_argument('--release-sha256',required=True);ap.add_argument('--attempt',required=True);a=ap.parse_args()
 # Import only named, exact reviewed helper definitions; never evaluate its CLI/body.
 helper=P/'capture-template-import-v4.py'
 assert raw_sha(helper)=='fccb520d6e04b3d9b8748153e4aa827ddfd949f4ad68106fc452cd2e7cdd11b5'
 names={'sha','bind','put','safe','git','state','runtime_snapshot','real','family_paths','own_family','validate_own_family','sealed_family_index','companion_membership','check_prior','exact_frozen_canary_headers','probe_output_paths','require_fresh_probe_outputs','verify_historical_input_maps'}
 tree=ast.parse(helper.read_text(encoding='utf-8'));nodes=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name in names];assert len(nodes)==len(names)
 import re
 env_helpers=dict(Path=Path,P=P,R=R,CACHE={},hashlib=hashlib,json=json,os=os,subprocess=subprocess,re=re,datetime=datetime)
 exec(compile(ast.Module(body=nodes,type_ignores=[]),str(helper),'exec'),env_helpers)
 bind=env_helpers['bind'];put=env_helpers['put'];state=env_helpers['state'];safe=env_helpers['safe'];runtime=env_helpers['runtime_snapshot'];membership=env_helpers['companion_membership']
 release=Path(a.release).resolve();assert release.is_relative_to(R/'tmp') and raw_sha(release)==a.release_sha256
 auth=read(release);assert auth['scope']=='STDOUT_OPERAND_DIAGNOSTIC_ONLY' and auth['Lean_resources_released'] is True and auth['diagnostic_Lean_authorized'] is True
 assert auth['independent_tool_review_accepted'] is True and bind(auth['independent_tool_review']['path'])==auth['independent_tool_review']
 recipe_names=['capture-operand-diagnostic-v1.py','ImportedOperandDiagnostic-construction-v1.lean','operand-diagnostic-construction-report-v1.json','capture-template-import-v4.py']
 assert auth['recipe']=={n:bind(P/n) for n in recipe_names}
 report_path=P/'operand-diagnostic-construction-report-v1.json';assert raw_sha(report_path)=='c256f5b99887d96fff6f21bc1fa1ad8a81afcb609a900cca8a61eaafa6d7c22c'
 report=read(report_path);src=Path(report['diagnostic']['path']);assert bind(src)==report['diagnostic'] and raw_sha(src)=='075cbf79313a0b3baf62dd7dc7dd0fbd11c9f6c2c298330b017dedb4de73b9c7'
 for row in report['fixed_inputs'].values():assert bind(row['path'])==row
 assert bind(report['compiler_Expr']['path'])==report['compiler_Expr']
 root_return=R/'tmp/online-support-resume-20261012/attainment-canary-v4-resource-return-v1.json'
 assert raw_sha(root_return)=='09d8a05014525931313f7299726647a6b9b7cc3a4213de130e26daeb5c329690'
 assert auth['prior_resource_return']==bind(root_return)
 assert sys.version_info[:3]==(3,12,14) and raw_sha(sys.executable)=='31073dad142bc7f3374e3122aa668270052c9ad37d0aaab803ae73f184c3a43b'
 expected=dict(head=auth['expected_head'],branch=auth['expected_branch'],status='');assert state()==expected
 out=safe(a.attempt);out.mkdir(exist_ok=False);record=diagnostic_outcome(None,False);code=1
 try:
  failed=read(P/'imported-v2/receipt.json');assert_failed_observation(failed,expected)
  pins=read(P/'capture-pins-import-v4.json')
  assert failed['argv']==[pins['compiler']['path'],str(P/'ImportedAudit-construction-v2.lean')] and Path(failed['cwd']).resolve()==R
  expected_env={'LEAN_NUM_THREADS':'2','LEAN_PATH':os.pathsep.join([str(P)]+pins['scratch_parent_roots']+pins['ordered_search_roots'])}
  assert failed['env_overrides']==expected_env
  inputs=env_helpers['verify_historical_input_maps']([failed])
  for row in [bind(P/'capture-pins-import-v4.json'),bind(P/'capture-import-v4.py'),pins['release'],pins['compiler']]:assert inputs[env_helpers['real'](row['path'])]==row
  mi=read(P/'import-input-manifest-v2.json');assert inputs[env_helpers['real'](P/'import-input-manifest-v2.json')]==bind(P/'import-input-manifest-v2.json')
  body=read(mi['receipt']['path']);assert bind(mi['receipt']['path'])==mi['receipt'] and body['actual_exit']==0 and body['integrity_pass'] is True
  assert body['output_family']==mi['output_family'] and body['output_olean']==mi['olean'];own=mi['output_family'];env_helpers['validate_own_family'](own)
  paths=[Path(x['path']) for x in inputs.values()]+[root_return,src,Path(__file__),report_path,helper,release,Path(auth['independent_tool_review']['path']),Path(report['compiler_Expr']['path'])]+[Path(x['path']) for x in report['fixed_inputs'].values()]
  paths += [Path(failed[k]['path']) for k in ['stdout','stderr']]
  for k in ['stdout','stderr']:assert bind(failed[k]['path'])==failed[k]
  paths=list(dict.fromkeys(x.resolve() for x in paths))
  before_runtime=runtime(pins);before_members=membership(pins,'import',own)
  assert before_runtime==failed['runtime_after'] and before_members==failed['companion_membership_after']
  record['seven_audit_paths_absent_before']=env_helpers['require_fresh_probe_outputs']()
  child_env={k:v for k,v in os.environ.items() if not k.upper().startswith('LEAN_')};child_env.update(expected_env)
  argv=[pins['compiler']['path'],str(src)]
  record.update(argv=argv,cwd=str(R),env_overrides=expected_env,pre_git=expected,before_RAW=[bind(x) for x in paths],runtime_before=before_runtime,companion_membership_before=before_members,start_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());put(out/'pre.json',record)
  with (out/'stdout.raw').open('xb') as stdout,(out/'stderr.raw').open('xb') as stderr:child=subprocess.run(argv,cwd=R,env=child_env,stdout=stdout,stderr=stderr)
  record.update(actual_exit=child.returncode,end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());env_helpers['CACHE'].clear()
  record.update(stdout=bind(out/'stdout.raw'),stderr=bind(out/'stderr.raw'));put(out/'child-result.json',{k:record[k] for k in ['actual_exit','end_utc','stdout','stderr']})
  record['seven_audit_paths_absent_after']=env_helpers['require_fresh_probe_outputs']()
  record.update(runtime_after=runtime(pins),companion_membership_after=membership(pins,'import',own),after_RAW=[bind(x) for x in paths],post_git=state())
  intact=record['before_RAW']==record['after_RAW'] and record['pre_git']==record['post_git'] and record['runtime_before']==record['runtime_after'] and record['companion_membership_before']==record['companion_membership_after']
  record.update(diagnostic_outcome(child.returncode,intact));code=child.returncode or (0 if intact else 1)
 except Exception as exc:record['error']=str(exc)
 finally:put(out/'receipt.json',record);print(json.dumps({k:record.get(k) for k in ['status','actual_exit','integrity_pass','canary_accepted','error']}))
 return code
if __name__=='__main__':sys.exit(main())
