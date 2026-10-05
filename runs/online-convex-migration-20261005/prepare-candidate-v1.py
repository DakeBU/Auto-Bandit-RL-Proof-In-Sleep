"""Record bounded compiled reuse candidate after current integrated roots."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-CONVEX-MIGRATION-20261005';base='a2728b1da2109844ffec64f594827197cd9b541b'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
    with (run/n).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
freeze=load(run/'draft-freeze-v1.json');token=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
for g,names in freeze['groups'].items():
    p=Path('BanditRLProof')/(g+'.lean');assert token(p.read_text(encoding='utf-8'))==token((run/('original-'+g+'.lean.txt')).read_text(encoding='utf-8'))
    for n in names:assert hashlib.sha256(lean_declaration_header(p,n).encode()).hexdigest()==freeze['headers'][n]
for p,h in freeze['canaries'].items():assert sha(p)==h,p
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
    assert load(run/(label+'-exit.json'))['exit_code']==0
    raw=(run/(label+'.log')).read_text(encoding='utf-8');m=re.search(r'Build completed successfully \((\d+) jobs\)',raw);assert m
    jobs[label]=int(m.group(1))
ready=load(run/'ready-dependencies-v1.json');assert sha(ready['graph_path'])==ready['graph_sha256']
changed=subprocess.check_output(['git','diff',base,'--name-only','--','*.lean'],encoding='utf-8').splitlines();assert sorted(changed)==sorted(freeze['modules'])
write('compiled-dependencies-v1.json',dict(status='validated-reuse-of-actual-compiled-shared-graph',graph_path=ready['graph_path'],graph_sha256=ready['graph_sha256'],extraction=ready['extraction'],scope_nodes=ready['scope_nodes'],actual_edges=ready['actual_edges'],boundary_nodes=ready['boundary_nodes'],required_actual_value_pairs=ready['required_actual_value_pairs'],only_Lean_delta_from_verified_stacked_base=changed,all_current_code_tokens_unchanged=True,same_toolchain_shared_root=True,fresh_jobs=jobs,new_export=False,canary_graph_export=False,teaching_edges_are_not_proof_dependencies=True))
write('memory-digest-candidate-v1.md','Four retained convex modules22proofs/five definitions, zero new proof/registry nodes. Distinct contract/body source reviews accepted with explicit real-space/upperAdd/zero-product deltas. Required three reader corrections addressed; all native headers/code tokens and canary bytes preserved. Fresh integrated root/Tests passed. Actual shared graph reuse27nodes/13required proof-value pairs, no new export. Full harness/final shared registry/site/reader/contributor/raw binding/PR gates pending. Whole Goal active, Chapter2 mandatory_totalnull; global SGB unchanged.')
write('retrieval-index-candidate-v1.md','Frozen22 headers/context/source card in docs/contracts/online-convex-migration-v1. Public terminals:theorem_2_4/examples2.5/2.6/three closure functions/convex_nonneg_linear_combination. Existing four public canary modules;53 actual named axiom outputs,22 native safe guards. Actual compiled dependency reuse:ready-dependencies-v1.json/compiled-dependencies-v1.json. Raw snapshots:historical-raw-supersession-v1.json; current/prior binding audit:review-history-audit-v1.json. Source/body/reader are separate phases, no wholeChapter count inferred.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
with (run/'candidate-scoped-trials-v1.jsonl').open('w',encoding='utf-8',newline='\n') as f:
    for t in trials:
        if t.get('task')==task:f.write(json.dumps(t)+'\n')
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=22,definitions=5,new_proofs=0,canary_modules=4,frozen_headers=freeze['headers'],fresh_jobs=jobs,remaining_gates=['full harness','contributor','site/registry/final reader','binding/PR'],chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; four retained convex foundation modules candidate only, Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(Path('BanditRLProof/OnlineConvexSums.lean'),'convex_nonneg_linear_combination'),'--declaration','BanditRL.OnlineConvex.convex_nonneg_linear_combination','--file','BanditRLProof/OnlineConvexSums.lean','--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineConvex.convex_upperAdd:compiled','--dependency','lean:BanditRL.OnlineConvex.convex_nonneg_mul:compiled','--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Current integrated retained convex candidate recorded; native scoped frontier/shadow, global SGB unchanged.')
