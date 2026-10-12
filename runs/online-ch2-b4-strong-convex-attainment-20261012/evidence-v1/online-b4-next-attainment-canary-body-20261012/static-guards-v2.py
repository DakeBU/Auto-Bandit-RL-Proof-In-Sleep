"""Isolated guards only; never invoke preparation/capture/Lean or real inventory."""
from pathlib import Path
import ast,json,hashlib,os,re
P=Path(__file__).resolve().parent
source=P/'capture-template-v2.py';tree=ast.parse(source.read_bytes())
names={'real','family_paths','own_family','validate_own_family','check_probe','companion_membership','exact_frozen_canary_headers'}
nodes=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name in names]
assert len(nodes)==len(names)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def bind(p):
 p=Path(p).resolve();return dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p))
ctx={'Path':Path,'json':json,'os':os,'re':re,'sha':sha,'bind':bind}
exec(compile(ast.Module(body=nodes,type_ignores=[]),str(source),'exec'),ctx)
base=P/'static-fixtures-v2';base.mkdir(exist_ok=False);results=[]
def setup(label,module='A'):
 root=base/label;root.mkdir();early=root/'early';late=root/'late';own=root/'own'
 for d in [early,late,own]:d.mkdir()
 op=late/(module+'.olean');op.write_bytes(b'sealed');private=late/(module+'.olean.private');private.write_bytes(b'companion')
 cl={'origins':[{'module':module,'olean':str(op.resolve())}],'inputs':[bind(op),bind(private)]}
 (own/'closure-manifest-v1.json').write_text(json.dumps(cl),encoding='utf-8')
 pins={'scratch_parent_roots':[str(early.resolve())],'ordered_search_roots':[str(late.resolve())]};ctx['P']=own.resolve()
 return root,early,late,own,pins,cl
def reject(label,f):
 try:f()
 except (AssertionError,KeyError):results.append(label)
 else:raise AssertionError('Not rejected: '+label)
root,early,late,own,pins,cl=setup('valid');ctx['companion_membership'](pins,'header');results.append('Valid sealed origin/family accepted')
for module in ['A','StrongConvexAttainmentCandidate','WeierstrassExtendedCandidate']:
 root,early,late,own,pins,cl=setup('shadow-'+module,module);(early/(module+'.olean')).write_bytes(b'shadow')
 reject('Earlier-root shadow '+module,lambda:ctx['companion_membership'](pins,'header'))
root,early,late,own,pins,cl=setup('import-shadow');(own/'A.olean').write_bytes(b'shadow')
op=own/'StrongConvexAttainmentCanaries.olean';op.write_bytes(b'new own');family=[bind(op)]
reject('Import prepended-root shadow',lambda:ctx['companion_membership'](pins,'import',family))
root,early,late,own,pins,cl=setup('new-companion');(late/'A.olean.server').write_bytes(b'new')
reject('Unsealed parent companion',lambda:ctx['companion_membership'](pins,'body'))
root,early,late,own,pins,cl=setup('changed-companion');(late/'A.olean.private').write_bytes(b'changed')
reject('Changed parent companion',lambda:ctx['companion_membership'](pins,'body'))
root,early,late,own,pins,cl=setup('missing-companion');cl['inputs'].append(dict(path=str((late/'A.olean.server').resolve()),bytes=1,sha256='missing'))
(own/'closure-manifest-v1.json').write_text(json.dumps(cl),encoding='utf-8')
reject('Deleted expected parent companion',lambda:ctx['companion_membership'](pins,'body'))
root,early,late,own,pins,cl=setup('own-family');op=own/'StrongConvexAttainmentCanaries.olean';assert ctx['own_family']()==[]
op.write_bytes(b'own');family=[bind(op)];ctx['companion_membership'](pins,'import',family);results.append('Own fresh exact family included in import accepted')
op.write_bytes(b'changed');reject('Changed own artifact',lambda:ctx['validate_own_family'](family))
op.write_bytes(b'own');(own/'StrongConvexAttainmentCanaries.olean.private').write_bytes(b'new')
reject('Own extra companion',lambda:ctx['validate_own_family'](family))
reject('Own body freshness sees complete family',lambda:None if ctx['own_family']()==[] else (_ for _ in ()).throw(AssertionError()))
root,early,late,own,pins,cl=setup('missing-own');reject('Missing own family',lambda:ctx['validate_own_family']([dict(path=str((own/'StrongConvexAttainmentCanaries.olean').resolve()),bytes=1,sha256='missing')]))
probe=own/'reviewed.lean';probe.write_bytes(b'reviewed');pb=bind(probe);pins['imported_probe']=pb;release={'recipe':{'ImportedAudit-construction-v1.lean':pb}}
ctx['check_probe'](pins,release,probe,{'probe':pb});results.append('Exact reviewed probe accepted')
wrong=own/'other.lean';wrong.write_bytes(b'reviewed');reject('Self-bound different probe path',lambda:ctx['check_probe'](pins,release,wrong,{'probe':bind(wrong)}))
probe.write_bytes(b'changed');reject('Changed reviewed probe bytes',lambda:ctx['check_probe'](pins,release,probe,{'probe':bind(probe)}))
ctx['exact_frozen_canary_headers']((P/'scratch-candidate-v1.lean').read_bytes(),(P/'scratch-frozen-whole-v1.txt').read_bytes());results.append('Frozen headers unchanged')
print(json.dumps({'status':'ISOLATED_GUARDS_PASS','cases':results,'count':len(results),'real_Lean_or_inventory_or_entrypoint_execution':False},indent=2))
