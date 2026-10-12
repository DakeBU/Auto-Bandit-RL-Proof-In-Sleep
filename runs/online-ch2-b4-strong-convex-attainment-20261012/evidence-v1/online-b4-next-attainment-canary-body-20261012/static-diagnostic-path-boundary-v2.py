"""Real extracted bind + wrapper adapter on isolated JSON-string paths only."""
from pathlib import Path
import ast,hashlib,json
P=Path(__file__).resolve().parent
helper=P/'capture-template-import-v4.py';raw=helper.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='fccb520d6e04b3d9b8748153e4aa827ddfd949f4ad68106fc452cd2e7cdd11b5'
tree=ast.parse(raw);definitions=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['sha','bind']]
assert len(definitions)==2
ctx={'Path':Path,'hashlib':hashlib,'CACHE':{}}
exec(compile(ast.Module(body=definitions,type_ignores=[]),str(helper),'exec'),ctx)
actual_bind=ctx['bind']
wrapper=P/'capture-operand-diagnostic-v2.py';wtree=ast.parse(wrapper.read_bytes())
main=next(n for n in wtree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
adapter=next(n for n in main.body if isinstance(n,ast.FunctionDef) and n.name=='bind')
ad={'Path':Path,'raw_bind':actual_bind}
exec(compile(ast.Module(body=[adapter],type_ignores=[]),str(wrapper),'exec'),ad)
bound=ad['bind'];fixture=P/'static-diagnostic-path-fixtures-v2';fixture.mkdir(exist_ok=False)
f=fixture/'input.json';f.write_bytes(b'{"fixture":true}\n');path=str(f.resolve());cases=[]
try:actual_bind(path)
except AttributeError:cases.append('V1 real helper rejects JSON string as reported')
else:raise AssertionError('V1 defect not reproduced')
# Every bind call in the wrapper, using its exact callee name, is handled by this adapter.
calls=[n for n in ast.walk(main) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='bind']
assert len(calls)>=10
for n in calls:
 ctx['CACHE'].clear();from_json=json.loads(json.dumps({'path':path}))['path']
 observed=bound(from_json);assert observed==actual_bind(Path(path))
 assert observed['sha256']==hashlib.sha256(f.read_bytes()).hexdigest()
 cases.append('real helper JSON string regression for bind call line '+str(n.lineno))
ctx['CACHE'].clear();assert bound(Path(path))==bound(path);cases.append('Path and JSON-string produce exact same complete binding')
missing=fixture/'missing'
try:bound(str(missing))
except FileNotFoundError:cases.append('missing JSON path still rejected')
else:raise AssertionError('missing path accepted')
ctx['CACHE'].clear();before=bound(path);f.write_bytes(b'changed');ctx['CACHE'].clear();after=bound(path);assert before!=after;cases.append('changed bytes detected after original phase cache clearing')
old=ast.parse((P/'capture-operand-diagnostic-v1.py').read_bytes())
for name in ['raw_sha','read','assert_failed_observation','diagnostic_outcome']:
 a=next(n for n in old.body if isinstance(n,ast.FunctionDef) and n.name==name)
 b=next(n for n in wtree.body if isinstance(n,ast.FunctionDef) and n.name==name)
 assert ast.dump(a)==ast.dump(b)
cases.append('all existing top-level guard/outcome functions AST identical')
result={'status':'STATIC_REAL_HELPER_REGRESSIONS_PASS','count':len(cases),'cases':cases,'entrypoint_Lean_or_inventory_executed':False}
with (P/'static-diagnostic-path-boundary-v2-result.json').open('x') as out:json.dump(result,out,indent=2)
print(json.dumps(result))
