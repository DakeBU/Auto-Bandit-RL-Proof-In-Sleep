"""Compare exact V2/V3 guards only on isolated fixtures, never real inventories."""
from pathlib import Path
import ast,json,hashlib,os,re
P=Path(__file__).resolve().parent
names={'real','family_paths','own_family','validate_own_family','check_probe','companion_membership','sealed_family_index'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def bind(p):
 p=Path(p).resolve();return dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p))
def load(version):
 tree=ast.parse((P/f'capture-template-v{version}.py').read_bytes())
 nodes=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name in names]
 ns={'Path':Path,'json':json,'os':os,'re':re,'sha':sha,'bind':bind}
 exec(compile(ast.Module(body=nodes,type_ignores=[]),f'exact-v{version}-helpers','exec'),ns)
 return ns
v2=load(2);v3=load(3);base=P/'static-index-fixtures-v3';base.mkdir(exist_ok=False)
cases=[]
def setup(label):
 root=base/label;root.mkdir();early=root/'early';late=root/'late';own=root/'own'
 for folder in [early,late,own]:folder.mkdir()
 (late/'M').mkdir();op=late/'M'/'Basic.olean';op.write_bytes(b'main')
 family=[op]
 for suffix in ['.olean.private','.olean.server','.extra.more','.olean.aux.json']:
  q=late/'M'/('Basic'+suffix);q.write_bytes(suffix.encode());family.append(q)
 irrelevant=late/'M'/'Basicx.olean';irrelevant.write_bytes(b'not a Basic family')
 cl={'origins':[{'module':'M.Basic','olean':str(op.resolve())}],'inputs':[bind(x) for x in family+[irrelevant]]}
 pins={'scratch_parent_roots':[str(early.resolve())],'ordered_search_roots':[str(late.resolve())]}
 return root,early,late,own,op,cl,pins
def run(label,mutate=None,stage='header',accepted=True):
 root,early,late,own,op,cl,pins=setup(label);own_rows=None
 if stage=='import':
  target=own/'StrongConvexAttainmentCanaries.olean';target.write_bytes(b'canary');own_rows=[bind(target)]
 if mutate:mutate(root,early,late,own,op,cl,pins,own_rows)
 (own/'closure-manifest-v1.json').write_text(json.dumps(cl),encoding='utf-8')
 values=[]
 for ns in [v2,v3]:
  ns['P']=own.resolve()
  try:values.append(('accept',ns['companion_membership'](pins,stage,own_rows)))
  except (AssertionError,KeyError) as e:values.append(('reject',str(e)))
 assert values[0]==values[1],(label,values)
 assert (values[0][0]=='accept')==accepted,(label,values)
 cases.append(dict(case=label,result=values[0][0],identical_returned_maps_or_error=True))
run('valid-edge-companions')
run('valid-import-own',stage='import')
def shadow(root,early,late,own,op,cl,pins,rows):
 (early/'M').mkdir();(early/'M'/'Basic.olean').write_bytes(b'shadow')
run('earlier-shadow',shadow,accepted=False)
def ownshadow(root,early,late,own,op,cl,pins,rows):
 (own/'M').mkdir();(own/'M'/'Basic.olean').write_bytes(b'shadow')
run('own-import-shadow',ownshadow,stage='import',accepted=False)
run('duplicate-root-alias',lambda root,early,late,own,op,cl,pins,rows:pins['ordered_search_roots'].append(str(late/'..'/'late')),accepted=False)
def alias(root,early,late,own,op,cl,pins,rows):
 row=dict(cl['inputs'][0]);row['path']=str(op.parent/'..'/'M'/op.name);cl['inputs'].append(row)
run('duplicate-input-alias',alias,accepted=False)
run('added-parent-companion',lambda root,early,late,own,op,cl,pins,rows:(op.parent/'Basic.new.extra').write_bytes(b'new'),accepted=False)
run('changed-parent-companion',lambda root,early,late,own,op,cl,pins,rows:(op.parent/'Basic.olean.private').write_bytes(b'changed'),accepted=False)
def missing(root,early,late,own,op,cl,pins,rows):
 cl['inputs'].append(dict(path=str(op.parent/'Basic.missing'),bytes=1,sha256='missing'))
run('deleted-parent-companion',missing,accepted=False)
run('wrong-sealed-origin',lambda root,early,late,own,op,cl,pins,rows:cl['origins'][0].update(olean=str(early/'M'/'Basic.olean')),accepted=False)
run('own-new-companion',lambda root,early,late,own,op,cl,pins,rows:(own/'StrongConvexAttainmentCanaries.olean.private').write_bytes(b'new'),stage='import',accepted=False)
run('own-changed-main',lambda root,early,late,own,op,cl,pins,rows:(own/'StrongConvexAttainmentCanaries.olean').write_bytes(b'changed'),stage='import',accepted=False)
# Index semantics checked against the original literal-prefix comprehension for dot edge names.
indexroot=base/'literal-index';indexroot.mkdir();sealed={}
for n in ['Basic.olean','Basic.olean.private','Basicx.olean','.hidden','A.B.olean','.olean.private','no_dot','Basic.']:
 f=indexroot/n;f.write_bytes(n.encode());sealed[v3['real'](f)]=bind(f)
index=v3['sealed_family_index'](sealed);parentkey=v3['real'](indexroot)
for stem in ['Basic','Basic.olean','Basicx','','A','A.B','no_dot','absent']:
 expected={k:row for k,row in sealed.items() if Path(row['path']).name.startswith(stem+'.') and v2['real'](Path(row['path']).parent)==parentkey}
 assert index.get((parentkey,stem),{})==expected
cases.append(dict(case='eight-literal-prefix-index-cases',result='accept',identical_returned_maps_or_error=True))
print(json.dumps({'status':'DIFFERENTIAL_FIXTURES_PASS','cases':cases,'case_count':len(cases),'index_subcases':8,'actual_Lean_or_inventory_or_entrypoint_execution':False},indent=2))
