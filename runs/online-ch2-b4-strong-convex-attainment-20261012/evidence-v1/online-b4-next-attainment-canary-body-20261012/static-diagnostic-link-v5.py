"""Pure receipt-schema checks, including actual saved data; no current inventory."""
from pathlib import Path
import ast,copy,datetime,json
P=Path(__file__).resolve().parent
source=P/'capture-template-import-v5.py';tree=ast.parse(source.read_text(encoding='utf-8'))
nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['validate_observed_diagnostic','probe_output_paths']]
assert len(nodes)==2;ctx={'P':P,'datetime':datetime};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(source),'exec'),ctx)
history=json.loads((P/'import-lineage-fixed-v5.json').read_text(encoding='utf-8'))
actual_diag=json.loads((P/'operand-diagnostic-v1/receipt.json').read_bytes());actual_failed=json.loads((P/'imported-v2/receipt.json').read_bytes())
ctx['validate_observed_diagnostic'](actual_diag,actual_failed,actual_diag['pre_git'],history)
cases=['actual saved diagnostic and failed-import schema/chronology accepted; no current file scan']
state={'head':'x','branch':'x','status':''};runtime={str(i):'h' for i in range(19)};paths=ctx['probe_output_paths']()
base=dict(pre_git=state,post_git=state,before_RAW=['same'],after_RAW=['same'],runtime_before=runtime,runtime_after=runtime,companion_membership_before=['same'],companion_membership_after=['same'],integrity_pass=True)
failed=dict(base,stage='import',actual_exit=1,end_utc='2020-01-01T00:00:00+00:00')
diag=dict(base,status='DIAGNOSTIC_ONLY_NOT_CANARY_ACCEPTANCE',canary_accepted=False,actual_exit=0,diagnostic_execution_succeeded=True,start_utc='2020-01-01T00:00:01+00:00',end_utc='2020-01-01T00:00:02+00:00',stdout='out',stderr='err',seven_audit_paths_absent_before=list(map(str,paths)),seven_audit_paths_absent_after=list(map(str,paths)))
hist={'diagnostic_stdout':'out','diagnostic_stderr':'err'};ctx['validate_observed_diagnostic'](diag,failed,state,hist);cases.append('synthetic diagnostic-only positive')
for key,value in [('status','ACCEPTED'),('canary_accepted',True),('actual_exit',1),('integrity_pass',False),('diagnostic_execution_succeeded',False),('post_git',{}),('after_RAW',[]),('runtime_after',{}),('companion_membership_after',[]),('start_utc','2019-01-01T00:00:00+00:00'),('stdout','other'),('stderr','other'),('seven_audit_paths_absent_after',[])]:
 bad=copy.deepcopy(diag);bad[key]=value
 try:ctx['validate_observed_diagnostic'](bad,failed,state,hist)
 except AssertionError:cases.append('reject diagnostic '+key)
 else:raise AssertionError(key)
for key,value in [('actual_exit',0),('stage','body'),('integrity_pass',False),('post_git',{}),('after_RAW',[])]:
 bad=copy.deepcopy(failed);bad[key]=value
 try:ctx['validate_observed_diagnostic'](diag,bad,state,hist)
 except AssertionError:cases.append('reject failed history '+key)
 else:raise AssertionError(key)
ast.parse((P/'prepare-import-v5.py').read_bytes())
result=dict(status='STATIC_DIAGNOSTIC_LINK_PASS',cases=cases,count=len(cases),capture_prepare_Lean_or_inventory_execution=False)
with (P/'static-diagnostic-link-v5-result.json').open('x') as f:json.dump(result,f,indent=2)
print(json.dumps(result))
