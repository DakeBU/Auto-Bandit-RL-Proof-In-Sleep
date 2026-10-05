"""Record compiled retained-proof candidate and task-local native frontier."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-FTL-MIGRATION-20261005'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
    with (run/n).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
freeze=load(run/'draft-freeze-v1.json')
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(Path('BanditRLProof/OnlineFTLFailure.lean'),n).encode()).hexdigest()==h,n
token=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert token(Path('BanditRLProof/OnlineFTLFailure.lean').read_text(encoding='utf-8'))==token((run/'original-public-module.lean.txt').read_text(encoding='utf-8'))
assert sha('Tests/OnlineFTLFailureCanary.lean')==freeze['original_public_canary_sha256']
for label in ['root-v1-01','Tests-v1-01']:assert load(run/(label+'-exit.json'))['exit_code']==0,label
root=(run/'root-v1-01.log').read_text(encoding='utf-8')
tests=(run/'Tests-v1-01.log').read_text(encoding='utf-8')
assert 'Build completed successfully (9087 jobs)' in root
assert 'Build completed successfully (9228 jobs)' in tests
ready=load(run/'ready-dependencies-v1.json')
assert sha(ready['graph_path'])==ready['graph_sha256']
changed=subprocess.check_output(['git','diff','4b55f5ebebb370ebe9e173b9bf5155b97a2e3998','--name-only','--','*.lean'],encoding='utf-8').splitlines()
assert changed==['BanditRLProof/OnlineFTLFailure.lean'],changed
write('compiled-dependencies-v1.json',dict(status='validated-reuse-of-actual-compiled-shared-graph',
    inherited_graph_receipt='runs/online-ogd-migration-20261005/accepted-decision-v2.json',
    graph_path=ready['graph_path'],graph_sha256=ready['graph_sha256'],extraction=ready['extraction'],
    scope_nodes=ready['scope_nodes'],actual_edges=ready['actual_edges'],boundary_nodes=ready['boundary_nodes'],
    required_actual_value_pairs=ready['required_actual_value_pairs'],
    only_Lean_delta_from_verified_stacked_base=changed,all_current_Lean_code_tokens_unchanged=True,
    same_toolchain_and_shared_root=True,fresh_root_jobs=9087,fresh_Tests_jobs=9228,
    new_export=False,canary_graph_export=False,teaching_edges_are_not_proof_dependencies=True))
write('memory-digest-candidate-v1.md','One retained FTL Example2.10 path only.7 old proofs/3 definitions, zero new proof/registry nodes. Distinct contract/body reviews passed with explicit fixed-x0/tie/index/minimization boundaries. Reader repaired and all Lean code tokens unchanged; fresh root9087/Tests9228 passed. Exact reused actual graph10 nodes/818edges/361boundary/six required value pairs, no new export. Full harness/site/registry/final reader/contributor/raw binding/PR pending; whole Goal ACTIVE, Chapter2 incomplete, global SGB unchanged. Administrative failed snapshots/trial enums/comment delimiter retained.')
write('retrieval-index-candidate-v1.md','Public terminal: BanditRL.OnlineLearning.example_2_10. Frozen native headers:docs/contracts/online-ftl-migration-v1. Source printed12/PDF24. Actual retained bodies/2 canaries:public-actual-bindings-v1.json. Independent contract/body reports and receipts in this run. Actual proof dependencies:ready-dependencies-v1.json/compiled-dependencies-v1.json. Historical bytes:historical-raw-supersession-v1.json. Fresh Chapter2 numbered navigation and18 unnumbered audit groups live in runs/online-ch2-enumeration-20261005; neither is a stabilized fullchapter contract.')
trialrows=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
with (run/'candidate-scoped-trials-v1.jsonl').open('w',encoding='utf-8',newline='\n') as f:
    for t in trialrows:
        if t.get('task')==task:f.write(json.dumps(t)+'\n')
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate',
    '--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=7,definitions=3,new_proofs=0,canaries=2,
        frozen_headers=freeze['headers'],root_jobs=9087,Tests_jobs=9228,remaining_gates=['full harness','site/registry/final reader','contributor/raw bindings/PR'],chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh',
    '--root-objective','Persistent Orabona Chapters1-16 Goal; retained FTL Example2.10 migration candidate only, Chapter2/book incomplete',
    '--leaf',task,'--kind','lean','--statement',lean_declaration_header(Path('BanditRLProof/OnlineFTLFailure.lean'),'example_2_10'),
    '--declaration','BanditRL.OnlineLearning.example_2_10','--file','BanditRLProof/OnlineFTLFailure.lean',
    '--source-status','source-body-reviewed','--leaf-status','gate-pending',
    '--dependency','lean:BanditRL.OnlineLearning.failure_prediction:compiled','--dependency','review:source-body:accepted',
    '--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow',
    '--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),
    '--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Compiled retained FTL candidate/task-local frontier and shadow recorded; global SGB unchanged, package gates pending.')
