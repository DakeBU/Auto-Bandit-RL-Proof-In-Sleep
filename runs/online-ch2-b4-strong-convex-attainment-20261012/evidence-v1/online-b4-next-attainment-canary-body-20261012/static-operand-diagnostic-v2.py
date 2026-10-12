"""Pure isolated receipt/outcome fixtures; no capture or inventory entrypoint."""
from pathlib import Path
import ast,copy,datetime,json
P=Path(__file__).resolve().parent
source=P/'capture-operand-diagnostic-v2.py';tree=ast.parse(source.read_text(encoding='utf-8'))
nodes=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name in ['assert_failed_observation','diagnostic_outcome']]
assert len(nodes)==2;ctx={'datetime':datetime};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(source),'exec'),ctx)
expected={'head':'same','branch':'same','status':''};runtime={str(i):'hash' for i in range(19)}
good=dict(stage='import',actual_exit=1,integrity_pass=True,pre_git=expected,post_git=expected,before_RAW=[{'p':'h'}],after_RAW=[{'p':'h'}],runtime_before=runtime,runtime_after=runtime,companion_membership_before=['same'],companion_membership_after=['same'],start_utc='2020-01-01T00:00:00+00:00',end_utc='2020-01-01T00:00:01+00:00')
cases=[];ctx['assert_failed_observation'](good,expected);cases.append('authentic failed audit retained')
for key,value in [('stage','body'),('actual_exit',0),('integrity_pass',False),('post_git',{}),('after_RAW',[]),('runtime_after',{}),('companion_membership_after',[]),('end_utc','2019-01-01T00:00:00+00:00')]:
 bad=copy.deepcopy(good);bad[key]=value
 try:ctx['assert_failed_observation'](bad,expected)
 except AssertionError:cases.append('reject '+key)
 else:raise AssertionError(key)
for code,intact in [(0,True),(0,False),(1,True),(None,False)]:
 result=ctx['diagnostic_outcome'](code,intact)
 assert result['status']=='DIAGNOSTIC_ONLY_NOT_CANARY_ACCEPTANCE' and result['canary_accepted'] is False
 assert result['diagnostic_execution_succeeded']==(code==0 and intact);cases.append('nonaccepting outcome '+str((code,intact)))
text=source.read_text(encoding='utf-8')
assert "argv=[pins['compiler']['path'],str(src)]" in text
assert "'seven_audit_paths_absent_before'" in text and "'seven_audit_paths_absent_after'" in text
assert "put(out/'child-result.json'" in text and text.index("put(out/'child-result.json'")<text.index("record['seven_audit_paths_absent_after']")
assert "ast.FunctionDef" in text and "len(nodes)==len(names)" in text
cases.append('exact read-only command, definition-only helper load and post-child retention guards')
result=dict(status='STATIC_ISOLATED_PASS',cases=cases,count=len(cases),actual_Lean_capture_or_inventory=False)
with (P/'static-operand-diagnostic-v2-result.json').open('x') as f:json.dump(result,f,indent=2)
print(json.dumps(result))
