"""Isolated function fixtures only: no operational entrypoint or Lean."""
from pathlib import Path
import ast,copy,hashlib,json,os
P=Path(__file__).resolve().parent
source=P/'capture-template-import-v4.py';tree=ast.parse(source.read_text())
names={'real','validate_pin_transport','validate_manifest_transport','verify_historical_input_maps','probe_output_paths','require_fresh_probe_outputs'}
nodes=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name in names]
assert len(nodes)==len(names)
def bind(p):
 p=Path(p).resolve();b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
fixture=P/'static-lineage-fixtures-v4';fixture.mkdir(exist_ok=False)
ctx=dict(Path=Path,os=os,bind=bind,P=fixture)
exec(compile(ast.Module(body=nodes,type_ignores=[]),str(source),'exec'),ctx)
cases=[]
def reject(name,fn):
 try:fn()
 except (AssertionError,KeyError,FileNotFoundError):cases.append(name)
 else:raise AssertionError('Accepted negative fixture: '+name)
prior=dict(compiler='compiler',runtime='runtime19',roots=['r1','r2'],closure='sealed',release='old',capture='oldcapture',imported_probe='oldprobe')
history={'probe_v2':'newprobe'};pins=dict(prior,release='new',capture='newcapture',imported_probe='newprobe',history=history)
ctx['validate_pin_transport'](prior,pins,history);cases.append('exact allowed pin transport')
for key in ['compiler','runtime','roots','closure']:
 bad=copy.deepcopy(pins);bad[key]='changed';reject('pin drift '+key,lambda:ctx['validate_pin_transport'](prior,bad,history))
oldmi=dict(candidate='samebody',olean='sameolean',receipt='passedbody',output_family=['sameolean'],probe='old',inputs=['old'])
mi=dict(oldmi,probe='new',inputs=['new']);ctx['validate_manifest_transport'](oldmi,mi,'new');cases.append('probe-only manifest transport')
for key in ['candidate','olean','receipt','output_family','inputs']:
 bad=copy.deepcopy(mi);bad[key]=[];reject('manifest drift '+key,lambda:ctx['validate_manifest_transport'](oldmi,bad,'new'))
f=fixture/'sealed';f.write_bytes(b'one');row=bind(f);receipt={'before_RAW':[row],'after_RAW':[row]}
ctx['verify_historical_input_maps']([receipt,receipt]);cases.append('complete historical map positive')
bad={'before_RAW':[row,row],'after_RAW':[row,row]};reject('duplicate historical path',lambda:ctx['verify_historical_input_maps']([bad]))
bad={'before_RAW':[row],'after_RAW':[]};reject('unequal prepost maps',lambda:ctx['verify_historical_input_maps']([bad]))
f.write_bytes(b'two');reject('current historical input drift',lambda:ctx['verify_historical_input_maps']([receipt]))
f.write_bytes(b'one');badrow=dict(row,sha256='bad');bad={'before_RAW':[badrow],'after_RAW':[badrow]};reject('historical cross-receipt disagreement',lambda:ctx['verify_historical_input_maps']([receipt,bad]))
paths=ctx['require_fresh_probe_outputs']();assert len(paths)==7;cases.append('all seven outputs absent')
for i,name in enumerate(paths):
 # Separate fixture parent for each existing output; do not remove or overwrite previous fixtures.
 one=fixture/str(i);one.mkdir();ctx['P']=one;(one/Path(name).name).write_bytes(b'partial')
 reject('existing output '+Path(name).name,ctx['require_fresh_probe_outputs'])
probe1=(P/'ImportedAudit-construction-v1.lean').read_bytes();probe2=(P/'ImportedAudit-construction-v2.lean').read_bytes()
assert probe1.count(b'.natLit?')==2 and probe1.replace(b'.natLit?',b'.rawNatLit?')==probe2;cases.append('two exact raw literal API corrections')
base=ast.parse((P/'capture-template-v3-final.py').read_text())
for name in ['runtime_snapshot','sealed_family_index','companion_membership','check_prior','exact_frozen_canary_headers','family_paths','validate_own_family']:
 a=next(x for x in base.body if isinstance(x,ast.FunctionDef) and x.name==name)
 b=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name==name)
 assert ast.dump(a)==ast.dump(b),name
cases.append('seven inherited guard function ASTs unchanged')
assert "choices=['import']" in source.read_text()
ast.parse((P/'prepare-import-v4.py').read_text())
result=dict(status='ISOLATED_STATIC_FIXTURES_PASS',cases=cases,count=len(cases),Lean_or_inventory_or_entrypoint_execution=False)
with (P/'static-import-lineage-v4-result.json').open('x') as out:json.dump(result,out,indent=2)
print(json.dumps(result))
