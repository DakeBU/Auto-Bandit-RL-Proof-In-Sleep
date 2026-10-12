from pathlib import Path
import json,hashlib,ast
P=Path(__file__).resolve().parent;R=P.parent.parent
D=R/'tmp/online-b4-next-weierstrass-body-20261012';F=R/'tmp/online-b4-next-weierstrass-canary-freeze-20261012'
def bind(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
def put(n,s):
 with (P/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
canonical=(F/'canonical-frozen-whole-v1.txt').read_text(encoding='utf-8')
assert hashlib.sha256(canonical.encode()).hexdigest()=='ced84f3338f8a4e00e25dcee27744d834082b9b936b4d65e903bcd22790257be'
frozen=canonical.replace('import BanditRLProof.OnlineWeierstrassExtended','import WeierstrassExtendedCandidate',1)
put('scratch-frozen-whole-v1.txt',frozen)
candidate=(P/'canonical-candidate-v1.lean').read_text(encoding='utf-8').replace('import BanditRLProof.OnlineWeierstrassExtended','import WeierstrassExtendedCandidate',1)
put('candidate-v1.lean',candidate)
put('HeaderElaboration-v1.lean',frozen.replace('theorem bottom_singleton_attains :','#check'))
cl=json.loads((D/'closure-manifest-v1.json').read_text(encoding='utf-8'))
cl['inputs']=[bind(Path(x['path'])) for x in cl['inputs']]
cl['inputs'] += [bind(D/'candidate-v2.lean'),bind(D/'WeierstrassExtendedCandidate.olean')]
cl['origins'] += [dict(module='WeierstrassExtendedCandidate',source=str(D/'candidate-v2.lean'),olean=str(D/'WeierstrassExtendedCandidate.olean'))]
cl['scope']='Current df2 refresh of conservative actual compiler-derived import superset plus accepted A3 scratch. Current canary compiler origins must reconcile; every source/lib+IR hash and companion membership is rechecked before/after each child.'
put('closure-manifest-v1.json',json.dumps(cl,indent=2)+'\n')
cap=(D/'capture-v2.py').read_text(encoding='utf-8').replace("pinfile=P/'capture-pins-v2.json'","pinfile=P/'capture-pins-v1.json'")
cap=cap.replace("assert src.read_bytes().split(b' := by\\n',1)[0]+b'\\n'==frozen", "assert src.read_bytes().split(b' := by\\n',1)[0]+b'\\n\\nend BanditRL.Tests.OnlineWeierstrassExtendedCanary\\n'==frozen")
cap=cap.replace('WeierstrassExtendedCandidate.olean','WeierstrassExtendedCanary.olean')
at="ap=argparse.ArgumentParser();"
functions='''def runtime_snapshot(pins):
 row=pins['runtime_inventory'];rp=Path(row['path']);assert bind(rp)==row
 inv=json.loads(rp.read_text());root=Path(inv['toolchain_root'])
 files={p.resolve() for p in (root/'bin').rglob('*') if p.is_file()}
 files |= {p.resolve() for p in (root/'lib').rglob('*') if p.is_file() and p.suffix.lower() in ['.dll','.so','.dylib']}
 expected={str(Path(p).resolve()):h for p,h in inv['files'].items()}
 actual={str(p):sha(p) for p in sorted(files)}
 assert len(actual)==19 and actual==expected,'Portable runtime membership/hash drift'
 return actual

def companion_membership(pins):
 cl=json.loads((P/'closure-manifest-v1.json').read_text());sealed={str(Path(x['path']).resolve()) for x in cl['inputs']}
 actual=set()
 for row in cl['origins']:
  op=Path(row['olean']);stem=op.name[:-6];bases=[op.parent]
  if '.lake/build/lib/lean' in op.as_posix():bases.append(Path(op.parent.as_posix().replace('/lib/lean','/ir')))
  for base in bases:
   actual.update(str(p.resolve()) for p in base.glob(stem+'.*') if p.is_file())
 assert actual <= sealed,'Unsealed current source-library companion'
 return sorted(actual)

'''
cap=cap.replace(at,functions+at)
cap=cap.replace("argv=[pins['compiler']['path']];target=None", "runtime_before=runtime_snapshot(pins);membership_before=companion_membership(pins)\n argv=[pins['compiler']['path']];target=None")
cap=cap.replace("record.update(argv=argv,", "record.update(runtime_before=runtime_before,companion_membership_before=membership_before,argv=argv,")
cap=cap.replace("record.update(actual_exit=z.returncode,", "runtime_after=runtime_snapshot(pins);membership_after=companion_membership(pins)\n record.update(runtime_after=runtime_after,companion_membership_after=membership_after,actual_exit=z.returncode,")
cap=cap.replace("record['pre_git']==record['post_git'] and record['before_RAW']==record['after_RAW']", "record['pre_git']==record['post_git'] and record['before_RAW']==record['after_RAW'] and runtime_before==runtime_after and membership_before==membership_after")
ast.parse(cap);put('capture-v1.py',cap)
pins=json.loads((D/'capture-pins-v2.json').read_text())
pins.update(release=bind(F/'ignored-Lean-resource-release-v1.json'),freeze=bind(F/'local-header-freeze-v1.json'),frozen_header=bind(P/'scratch-frozen-whole-v1.txt'),canonical_header=bind(F/'canonical-frozen-whole-v1.txt'),header_probe=bind(P/'HeaderElaboration-v1.lean'),capture=bind(P/'capture-v1.py'),closure_manifest_sha256=bind(P/'closure-manifest-v1.json')['sha256'],scratch_parent_roots=[str(D)])
pins['parents'] += [bind(D/'candidate-v2.lean'),bind(D/'WeierstrassExtendedCandidate.olean')]
pins['project']=[bind(R/n) for n in ['lean-toolchain','lakefile.lean','lake-manifest.json','BanditRLProof.lean','Tests.lean']]
pins['runtime_inventory']=bind(R/'tmp/online-b4-next-dual-stability-alpha-comparator-20261012/v5/toolchain-runtime-inventory-v1.json')
put('capture-pins-v1.json',json.dumps(pins,indent=2)+'\n')
print(json.dumps(dict(pins=bind(P/'capture-pins-v1.json'),candidate=bind(P/'candidate-v1.lean'))))
