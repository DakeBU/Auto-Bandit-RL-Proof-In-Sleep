"""Integrate only actually compiled frozen diagnostic proofs; original producers fixed."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
assert load(run/'boundary-leaf-v2-01-exit.json')['exit_code']==0
assert load(run/'retained-public-axioms-v1-01-exit.json')['exit_code']==0
assert 'sorryAx' not in (run/'retained-public-axioms-v1-01.log').read_text(encoding='utf-8')
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineSubgradientDifferentiability.lean')
for group in ['module','whole_old_canary','fixed_shared_files']:
 for p,h in freeze[group].items():assert sha(p)==h,p
headers=load('docs/contracts/online-subgradient-differentiability-migration-v1/new-canary-terminals-v1.json')['headers']
scratch=run/'leaves/new-boundary-canary-v2.lean'
for n,row in headers.items():assert lean_declaration_header(scratch,n)==row['statement'],n
dest=Path('Tests/OnlineDifferentiabilityBoundaryCanary.lean');assert not dest.exists();dest.write_bytes(scratch.read_bytes())
root=Path('Tests.lean');original=(run/'original-Tests.lean.txt').read_bytes();assert root.read_bytes()==original
root.write_bytes(original+b'\nimport Tests.OnlineDifferentiabilityBoundaryCanary\n')
names=load(run/'public-named-declarations-v1.json')['axiom_probe']+['Tests.OnlineDifferentiabilityBoundary.'+n for n in headers]
assert len(names)==len(set(names))==20
probe=run/'leaves/public-all-axioms-v1.lean';assert not probe.exists()
probe.write_bytes(('import BanditRLProof\nimport Tests.OnlineSubgradientDifferentiabilityCanary\nimport Tests.OnlineDifferentiabilityBoundaryCanary\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names)).encode())
record=dict(status='compiled diagnostic scratch integrated; public gates pending',module_sha256=sha(public),whole_old_canary_fixed=True,new_canary=dest.as_posix(),new_canary_sha256=sha(dest),new_canary_proofs=3,new_canary_definitions=0,retained_public_proofs=11,retained_public_definitions=1,new_production_proofs=0,new_production_definitions=0,new_canary_headers_unchanged=True,Tests_raw_original_prefix=True,named_axiom_targets=names,kernel_probe=dict(path=probe.as_posix(),sha256=sha(probe)),source_body_accepted=False,chapter_complete=False,goal_complete=False)
out=run/'canary-integration-before-public-use-v1.json';assert not out.exists();out.write_bytes((json.dumps(record,indent=2)+'\n').encode())
print('Actual compiled fixed3diagnostics integrated;20named publickernel targets bound before use; all original production math fixed.')
