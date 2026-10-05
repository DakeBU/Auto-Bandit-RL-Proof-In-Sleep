"""Verify the distinct contract receipt, then record bounded retained-proof reuse."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent
module=Path('BanditRLProof/OnlineFTLFailure.lean')
canary=Path('Tests/OnlineFTLFailureCanary.lean')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
    with (run/n).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):
    subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
receipt=load(run/'source-contract-receipt-v1.json')
assert receipt['actor']['task']=='/root/source_reviewer'
assert receipt['verdict']=='accepted-with-explicit-delta' and not receipt['required_repairs']
assert sha(receipt['report'])==receipt['report_sha256']
inventory=load(run/'contract-source-inputs-v1.json')
reviewed={r['path']:r['sha256'] for r in receipt['reviewed_files']}
assert len(inventory['rows'])==92 and len(reviewed)==93
for r in inventory['rows']:assert reviewed[r['path']]==r['sha256']
for p,h in reviewed.items():assert sha(p)==h,p
freeze=load(run/'draft-freeze-v1.json')
assert set(receipt['target_verdicts'])==set(freeze['headers'])
assert all(v=='accepted-with-explicit-delta' for v in receipt['target_verdicts'].values())
report=Path(receipt['report']).read_text(encoding='utf-8')
for name in freeze['headers']:assert '| '+name+' |' in report,name
assert sha(module)==freeze['original_public_module_sha256']
assert sha(canary)==freeze['original_public_canary_sha256']
for n,h in freeze['headers'].items():
    assert hashlib.sha256(lean_declaration_header(module,n).encode()).hexdigest()==h,n
ready=load(run/'ready-dependencies-v1.json')
assert sha(ready['graph_path'])==ready['graph_sha256']
assert ready['scope_nodes']==10 and len(ready['required_actual_value_pairs'])==6
write('contract-binding-audit-v1.json',dict(status='passed',raw_review_rows=93,
    distinct_actor=receipt['actor']['task'],report_sha256=receipt['report_sha256'],
    reviewed_headers=freeze['headers'],semantic_slots_per_target=7,
    verdict=receipt['verdict'],remaining_body_package_gates=True))
gate('stabilized-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event',
    '--session','ONLINE-FTL-MIGRATION-20261005','--event','stabilized','--payload-json',
    json.dumps(dict(run_id=run.name,contract_version=1,source_contract_receipt=str(run/'source-contract-receipt-v1.json'),
        frozen_headers=freeze['headers'],definitions=3,retained_proofs=7,new_proofs=0,
        body_package_accepted=False,chapter_complete=False,goal_complete=False)))
gate('proving-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event',
    '--session','ONLINE-FTL-MIGRATION-20261005','--event','proving','--payload-json',
    json.dumps(dict(run_id=run.name,route='single lower route: inspect and freshly compile retained actual recursive FTL proofs',
        first_ready_leaf='prefixCoefficient_eq_sum',dependency_graph='reused compiled shared graph; readiness only',
        terminal='BanditRL.OnlineLearning.example_2_10',new_proofs=0,
        allowed_edit_scope=['source-qualified OnlineFTLFailure comments only','task-local evidence','scoped shared Book/manifest integration'],
        frozen_headers=freeze['headers'],chapter_complete=False,goal_complete=False)))
ob=load(run/'proof-obligations-v1.json')
for row in ob['required']:row['state']='source-stabilized-retained-body-fresh-verification-pending'
ob.update(stage='proving',source_contract_verdict=receipt['verdict'],new_proofs=0,
    dependency_readiness=str(run/'ready-dependencies-v1.json'))
write('proof-obligations-proving-v1.json',ob)
write('30_lower_worker-body-audit-v1.md',
    'Retained proof bodies inspected before fresh elaboration. prefixCoefficient_eq_sum uses induction over the actual recursive accumulator. '
    'linearFTLPredict_prefix rewrites that identity and finite-sum congruence, so only i<t matters for fixed x0. '
    'Membership unfolds the actual branch selector. Minimization factors the prefix objective S_t*x; t=0 objectives vanish, '
    'while negative/nonnegative S_t selects respectively +1/-1 and compares using comparator interval bounds. '
    'failure_prefixCoefficient is actual recurrence/parity induction, not an assumed prefix formula. '
    'failure_prediction substitutes that producer into the actual selector. example_2_10 derives every positive-time played loss=1, '
    'inducts the cumulative played losses, accounts for the exceptional -x0/2 first loss, and uses x0<=1 for the lower bound. '
    'The actual terminal is equality AND T-3/2 bound for T>0 and every feasible x0. No desired regret, stability, or future-output premise is assumed. '
    'Seven old proofs and three definitions reused; zero new theorem bodies or weakened targets. Fresh compilation/canaries/axioms/body-review and integrated/package gates still pending.')
names=['BanditRL.OnlineLearning.'+n for n in ['prefixCoefficient','linearFTLPredict','failureCoefficient']+list(freeze['headers'])]
names+=['Tests.OnlineFTLFailure.six_rounds','Tests.OnlineFTLFailure.actual_predictions']
assert len(names)==12 and len(set(names))==12
(run/'leaves').mkdir(exist_ok=True)
probe='import BanditRLProof\nimport Tests.OnlineFTLFailureCanary\n\n'
for n in names:probe+='#check @'+n+'\n#print axioms '+n+'\n'
with (run/'leaves/public-axioms-v1.lean').open('w',encoding='utf-8',newline='\n') as f:f.write(probe)
write('public-named-declarations-v1.json',dict(axiom_probe=names,proofs=7,definitions=3,canary_proofs=2))
print('Distinct source contract verified:93 raw rows; native stabilized/proving recorded; retained-body audit and12 actual axiom targets prepared.')
