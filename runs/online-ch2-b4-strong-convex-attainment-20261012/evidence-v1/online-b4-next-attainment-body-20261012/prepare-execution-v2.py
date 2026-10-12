"""Preparation only. Run only after an externally supplied new 6.9 Lean lease.
Does not launch Lean; creates exclusive pins and a refreshed full inventory.
"""
from pathlib import Path
import argparse,ast,hashlib,json,subprocess
P=Path(__file__).resolve().parent;R=P.parent.parent
D=R/'tmp/online-b4-next-weierstrass-canary-body-20261012'
A=R/'tmp/online-b4-next-weierstrass-body-20261012'
F=R/'tmp/online-b4-next-attainment-header-freeze-20261012'
if not __debug__:raise SystemExit('Refuse optimized Python')
def bind(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
def put(n,s):
 with (P/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
def git(*a):return subprocess.check_output(['git','-c','core.longpaths=true',*a],cwd=R).decode().strip()
ap=argparse.ArgumentParser();ap.add_argument('--release',required=True);ap.add_argument('--release-sha256',required=True)
for key in ['discovery-manifest','discovery-manifest-sha256','discovery-receipt','discovery-receipt-sha256']:ap.add_argument('--'+key,required=True)
a=ap.parse_args();release=Path(a.release).resolve();assert release.is_relative_to(R/'tmp')
assert bind(release)['sha256']==a.release_sha256
auth=json.loads(release.read_text(encoding='utf-8'))
assert auth.get('Lean_resources_released') is True
assert auth.get('Theorem6_9_Lean_execution_authorized') is True
assert git('rev-parse','HEAD')==auth['expected_head'] and git('branch','--show-current')==auth['expected_branch'] and not git('status','--porcelain','--untracked-files=all')
canonical=(F/'Theorem6.9-frozen-context-and-header-v1.txt').read_text(encoding='utf-8')
assert hashlib.sha256(canonical.encode()).hexdigest()=='58decad0d7dbd318b0c21949d2f699893df9059cb70dfd3fcee020a8ee12b1a5'
frozen=canonical.replace('import BanditRLProof.OnlineWeierstrassExtended','import WeierstrassExtendedCandidate',1)
put('scratch-frozen-header-v1.txt',frozen)
probe=frozen.replace('theorem stronglyConvex_existsUnique_minimizer {E : Type*}','#check ∀ {E : Type*}').replace(' :\n    ∃! p',',\n    ∃! p')+'\nend BanditRL.OnlineConvex\n'
put('HeaderElaboration-v1.lean',probe)
mp=Path(a.discovery_manifest).resolve();rp=Path(a.discovery_receipt).resolve()
assert mp.is_relative_to(R/'tmp') and rp.is_relative_to(R/'tmp')
assert bind(mp)['sha256']==a.discovery_manifest_sha256 and bind(rp)['sha256']==a.discovery_receipt_sha256
cl=json.loads(mp.read_text(encoding='utf-8'));dr=json.loads(rp.read_text(encoding='utf-8'))
assert dr['actual_exit']==0 and dr['integrity_pass']
assert dr['pre_git']==dr['post_git']==dict(head=auth['expected_head'],branch=auth['expected_branch'],status='')
assert dr['before_RAW']==dr['after_RAW']
assert dr['runtime_before']==dr['runtime_after'] and len(dr['runtime_before'])==19
assert dr['companion_membership_before']==dr['companion_membership_after']
assert dr['discovery_manifest']==bind(mp)
assert cl['origin_probe']==bind(P/'HeaderImportDiscovery-v2.lean')
assert str((P/'HeaderImportDiscovery-v2.lean').resolve()) in dr['argv']
assert cl['origin_output']==bind(P/'header-import-origins-v2.json')
observed=json.loads((P/'header-import-origins-v2.json').read_text(encoding='utf-8'))
assert len({x['module'] for x in cl['origins']})==len(cl['origins'])
assert {x['module']:str(Path(x['olean']).resolve()).lower() for x in observed}=={x['module']:str(Path(x['olean']).resolve()).lower() for x in cl['origins']}
required={'BanditRLProof.OnlineStrongConvexSourceSubgradient','BanditRLProof.OnlineStrongConvexMinimum','WeierstrassExtendedCandidate','Mathlib.Analysis.Normed.Module.FiniteDimension'}
assert required <= {x['module'] for x in cl['origins']},'Missing actual frozen-header direct import'
pre={str(Path(x['path']).resolve()).lower():x for x in dr['before_RAW']}
for row in cl['inputs']:
 pp=Path(row['path']);assert bind(pp)==row and pre[str(pp.resolve()).lower()]==row
cl['scope']='Exact transitive origin map from separately authorized current frozen-header import discovery; all current source/lib+IR files and runtime19 covered by authenticated unchanged discovery pre/post maps. Extra audit-module imports disclosed.'
cl['authenticated_discovery_receipt']=bind(rp)
put('closure-manifest-v1.json',json.dumps(cl,indent=2)+'\n')
cap=(D/'capture-v2.py').read_text(encoding='utf-8').replace("pinfile=P/'capture-pins-v2.json'","pinfile=P/'capture-pins-v1.json'")
cap=cap.replace('WeierstrassExtendedCanary.olean','StrongConvexAttainmentCandidate.olean')
cap=cap.replace("+b'\\n\\nend BanditRL.Tests.OnlineWeierstrassExtendedCanary\\n'==frozen","+b'\\n'==frozen")
ast.parse(cap);put('capture-v1.py',cap)
pins=json.loads((D/'capture-pins-v2.json').read_text(encoding='utf-8'))
pins.update(release=bind(release),freeze=bind(F/'Theorem6.9-local-header-freeze-v1.json'),frozen_header=bind(P/'scratch-frozen-header-v1.txt'),canonical_header=bind(F/'Theorem6.9-frozen-context-and-header-v1.txt'),header_probe=bind(P/'HeaderElaboration-v1.lean'),capture=bind(P/'capture-v1.py'),closure_manifest_sha256=bind(P/'closure-manifest-v1.json')['sha256'],scratch_parent_roots=[str(A)])
pins['project']=[bind(R/n) for n in ['lean-toolchain','lakefile.lean','lake-manifest.json','BanditRLProof.lean','Tests.lean']]
put('capture-pins-v1.json',json.dumps(pins,indent=2)+'\n')
print(json.dumps(dict(status='PREPARED_NOT_EXECUTED',pins=bind(P/'capture-pins-v1.json'))))
