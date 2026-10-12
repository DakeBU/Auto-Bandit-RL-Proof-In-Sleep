"""Create ignored V5 recipes only after the actual root return binding exists."""
from pathlib import Path
import argparse,ast,hashlib,json,difflib
P=Path(__file__).resolve().parent;R=P.parent.parent
def rec(p):
 p=Path(p).resolve();h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
def put(n,v):
 b=v if isinstance(v,bytes) else (json.dumps(v,indent=2)+'\n').encode()
 with (P/n).open('xb') as f:f.write(b)
ap=argparse.ArgumentParser();ap.add_argument('--root-return',required=True);ap.add_argument('--root-return-sha256',required=True);a=ap.parse_args()
ret=Path(a.root_return);assert rec(ret)['sha256']==a.root_return_sha256
history=json.loads((P/'import-lineage-fixed-v4.json').read_text(encoding='utf-8'))
extra={'probe_v3':'ImportedAudit-construction-v3.lean','failed_import_v2':'imported-v2/receipt.json','diagnostic_report':'operand-diagnostic-actual-and-strict-proposal-v1.json','diagnostic_receipt':'operand-diagnostic-v1/receipt.json','diagnostic_stdout':'operand-diagnostic-v1/stdout.raw','diagnostic_stderr':'operand-diagnostic-v1/stderr.raw','diagnostic_source':'ImportedOperandDiagnostic-construction-v1.lean'}
history.update({k:rec(P/n) for k,n in extra.items()});history['diagnostic_return']=rec(ret)
assert history['probe_v3']['sha256']=='ce11635e7fa59ac9b5e3068729c3662f7509be04093665243092daa4c927cdb4'
assert history['diagnostic_report']['sha256']=='6f207a4ad1a1d4d8b3120f4f4696345822feb2b9106f199685a0036ac1a6808c'
assert history['diagnostic_receipt']['sha256']=='837932c657c801a789bd783714cb0113f1e4e164aaba764da45b30e686a59cb8'
assert history['failed_import_v2']['sha256']=='8ee557a94ca0d597434fb7e8d901c69618003b1698e9a48c8fe8237127b5f331'
put('import-lineage-fixed-v5.json',history);fixed=rec(P/'import-lineage-fixed-v5.json')
base=(P/'capture-template-import-v4.py').read_text(encoding='utf-8');s=base
for old,new in [('ImportedAudit-construction-v2.lean','ImportedAudit-construction-v3.lean'),('prepare-import-v4.py','prepare-import-v5.py'),('capture-template-import-v4.py','capture-template-import-v5.py'),('import-lineage-fixed-v4.json','import-lineage-fixed-v5.json'),('capture-pins-import-v4.json','capture-pins-import-v5.json')]:s=s.replace(old,new)
# Preserve real historical v1/v2 probe rows; only the operative probe selector changes.
s=s.replace("imported_probe=history['probe_v2']","imported_probe=history['probe_v3']")
start=s.index('FIXED_LINEAGE=');end=s.index('\n',start);s=s[:start]+'FIXED_LINEAGE='+repr(fixed)+s[end:]
old="root_return=R/'tmp/online-support-resume-20261012/attainment-canary-v3-resource-return-v2.json'\n assert sha(root_return)=='af57721df0dad004827b5e9623a003536cf9135f961c0a16b5ebe33bd895427f'"
assert old in s;s=s.replace(old,"root_return=Path(history['diagnostic_return']['path'])\n assert bind(root_return)==history['diagnostic_return']")
fn='''def validate_observed_diagnostic(diag,failed,before,history):
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

'''
s=s.replace('def authenticate_import_lineage(',fn+'def authenticate_import_lineage(',1)
s=s.replace(' allrows=verify_historical_input_maps([hr,br])'," diag=json.loads(Path(history['diagnostic_receipt']['path']).read_text());failed=json.loads(Path(history['failed_import_v2']['path']).read_text())\n validate_observed_diagnostic(diag,failed,before,history)\n assert diag['argv']==[prior['compiler']['path'],history['diagnostic_source']['path']] and Path(diag['cwd']).resolve()==R\n assert failed['argv']==[prior['compiler']['path'],history['probe_v2']['path']] and Path(failed['cwd']).resolve()==R\n expected_env={'LEAN_NUM_THREADS':'2','LEAN_PATH':os.pathsep.join([str(P)]+prior['scratch_parent_roots']+prior['ordered_search_roots'])}\n assert diag['env_overrides']==failed['env_overrides']==expected_env\n allrows=verify_historical_input_maps([hr,br,failed,diag])")
s=s.replace(' for receipt in [hr,br]:paths +=', ' for receipt in [hr,br,failed,diag]:paths +=')
# Authenticate earlier failed stdout/stderr as well as binding them into the new maps.
s=s.replace(" for receipt in [hr,br,failed,diag]:paths += [Path(receipt[k]['path']) for k in ['stdout','stderr']]", " for receipt in [hr,br,failed,diag]:\n  for k in ['stdout','stderr']:\n   assert bind(Path(receipt[k]['path']))==receipt[k];paths.append(Path(receipt[k]['path']))")
ast.parse(s);put('capture-template-import-v5.py',s.encode())
prepare=(P/'prepare-import-v4.py').read_text(encoding='utf-8');new=prepare
for old,successor in [('prepare-import-v4.py','prepare-import-v5.py'),('capture-template-import-v4.py','capture-template-import-v5.py'),('ImportedAudit-construction-v2.lean','ImportedAudit-construction-v3.lean'),('import-lineage-fixed-v4.json','import-lineage-fixed-v5.json'),('capture-import-v4.py','capture-import-v5.py'),('capture-pins-import-v4.json','capture-pins-import-v5.json'),('import-input-manifest-v2.json','import-input-manifest-v3.json')]:new=new.replace(old,successor)
new=new.replace('fccb520d6e04b3d9b8748153e4aa827ddfd949f4ad68106fc452cd2e7cdd11b5',rec(P/'capture-template-import-v5.py')['sha256']).replace('6ce6e874ab23bd21d17b32d21b365ee950bcde7080712350f063bee0aa303d36',fixed['sha256'])
old="root_return=R/'tmp/online-support-resume-20261012/attainment-canary-v3-resource-return-v2.json'\n    assert bind(root_return)['sha256']=='af57721df0dad004827b5e9623a003536cf9135f961c0a16b5ebe33bd895427f'"
assert old in new;new=new.replace(old,"root_return=Path("+repr(str(ret.resolve()))+")\n    assert bind(root_return)=="+repr(rec(ret)))
old="old=Path(history['probe_v1']['path']).read_bytes();new=Path(history['probe_v2']['path']).read_bytes()\n    assert old.count(b'.natLit?')==2 and old.replace(b'.natLit?',b'.rawNatLit?')==new"
assert old in new;new=new.replace(old,"diagnostic_report=json.loads(Path(history['diagnostic_report']['path']).read_text())\n    assert diagnostic_report['proposal']==history['probe_v3'] and diagnostic_report['prior_probe']==history['probe_v2']\n    assert diagnostic_report['receipt']==history['diagnostic_receipt'] and diagnostic_report['stdout']==history['diagnostic_stdout']\n    assert history['probe_v3']['sha256']=='ce11635e7fa59ac9b5e3068729c3662f7509be04093665243092daa4c927cdb4'")
new=new.replace("imported_probe=history['probe_v2']","imported_probe=history['probe_v3']").replace("mi.update(probe=history['probe_v2'],inputs=[history['probe_v2']])","mi.update(probe=history['probe_v3'],inputs=[history['probe_v3']])")
ast.parse(new);put('prepare-import-v5.py',new.encode())
put('capture-import-v4-to-v5.diff',''.join(difflib.unified_diff(base.splitlines(True),s.splitlines(True),fromfile='accepted-importV4',tofile='proposed-importV5')).encode())
put('prepare-import-v4-to-v5.diff',''.join(difflib.unified_diff(prepare.splitlines(True),new.splitlines(True),fromfile='accepted-prepareV4',tofile='proposed-prepareV5')).encode())
print(json.dumps({'capture':rec(P/'capture-template-import-v5.py'),'prepare':rec(P/'prepare-import-v5.py'),'fixed':fixed}))
