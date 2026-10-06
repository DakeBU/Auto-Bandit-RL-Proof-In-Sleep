"""Check distinct contract acceptance before revalidating retained producer bodies."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-SUM-MIGRATION-20261007'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes((x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
receipt=load(run/'source-contract-receipt-v1.json')
assert receipt['actor']['task']=='/root/source_reviewer' and receipt['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not receipt.get('mathematical_repairs',[]) and not receipt.get('required_mathematical_repairs',[]) and not receipt.get('required_repairs',[])
assert sha(receipt['report'])==receipt['report_sha256']
reviewed={r['path']:r['sha256'] for r in receipt['reviewed_files']}
for row in load(run/'contract-source-inputs-v2.json')['rows']:
 assert reviewed[row['path']]==row['sha256']==sha(row['path']),row['path']
for p,h in reviewed.items():assert sha(p)==h,p
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineSubgradientSum.lean')
for group in ['module','whole_old_canary','fixed_shared_files']:
 for p,h in freeze[group].items():assert sha(p)==h,p
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=receipt['report_sha256'],retained_proofs=9,retained_definitions=1,new_production_proofs=0,required_reader_corrections=receipt.get('required_reader_corrections',[]),all_current_fixed_inputs_rehashed=True,frozen_headers_unchanged=True))
write('proof-obligations-proving-v1.json',dict(stage='proving',required=[dict(name=n,statement_hash=h,state='stabilized-source-contract; actual retained body revalidation pending') for n,h in freeze['headers'].items()],required_complete_definition='SourceSubgradientSum',source_branches=2,retained_proofs=9,new_production_proofs=0,whole_canary_proofs=20,whole_canary_definitions=3,source_package_accepted=False,chapter_complete=False,goal_complete=False))
write('30_lower_worker-v1.md','Single retained body revalidation route after distinct CONTRACT: nine exact source refinements/full actualM/whole20canaryproofs3defs remain byte-exact. Actual binary separation strictnegative heightcoefficient and derivedqueryfinite/inductive Fin.snoc witnesses inspected. Actualbody build/wholecanary/canonical type/kernel29/nativeguards9/selectedcompiledgraph still separately required. No weak consumer replacement/source-condition deletion/duplicate wrappers/newmathclaim. Main and Book Goal remain incomplete.')
named=load(run/'public-named-declarations-v1.json')
assert len(named['axiom_probe'])==len(set(named['axiom_probe']))==29
write('leaves/public-all-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineSubgradientSumCanary\n'+''.join('#print axioms '+n+'\n' for n in named['axiom_probe']))
old=Path('runs/online-subgradient-differentiability-migration-20261007/leaves/export-public-dependencies-v1.lean')
t=old.read_text(encoding='utf-8');a=t.index('def targets');b=t.index('\ndef moduleName')
targets=named['public_proofs']+named['public_definitions']+named['whole_canary_proofs']+named['whole_canary_definitions']
assert len(targets)==len(set(targets))==33
t=t[:a]+'def targets : Array Name := #[\n  '+',\n  '.join('`'+n for n in targets)+']\n'+t[b:]
t=t.replace('Tests.OnlineSubgradientDifferentiabilityCanary','Tests.OnlineSubgradientSumCanary')
t=t.replace(', { module := `Tests.OnlineDifferentiabilityBoundaryCanary }','')
t=t.replace('eleven retained producer proofs, one complete definition and nine old/new canary proofs; selected direct type/value boundary only; not full registry graph','nine retained sum-rule proofs, one complete Minkowski definition, twenty whole canary proofs and three canary definitions; direct type/value boundary only')
assert 'OnlineDifferentiabilityBoundaryCanary' not in t
write('leaves/export-public-dependencies-v1.lean',t)
write('proving-generated-before-use-v1.json',dict(rows=[dict(path=(run/n).as_posix(),sha256=sha(run/n)) for n in ['leaves/public-all-axioms-v1.lean','leaves/export-public-dependencies-v1.lean']],before_first_use=True,math_headers_fixed=True))
gate('stabilized-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','stabilized','--payload-json',json.dumps(dict(run_id=run.name,contract_receipt=str(run/'source-contract-receipt-v1.json'),retained_proofs=9,full_witness_definition_fixed=True,source_package_accepted=False,chapter_complete=False,goal_complete=False)))
gate('proving-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','proving','--payload-json',json.dumps(dict(run_id=run.name,route='single retained actualproducer body',allowed_math_mutations=False,source_branches=2,source_package_accepted=False,chapter_complete=False,goal_complete=False)))
print('Distinct CONTRACT bound, actual retained producer revalidation permitted;29namedkernel and33selectednodes probes prepared, not yet executed.')
