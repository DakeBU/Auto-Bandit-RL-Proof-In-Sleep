"""Record the retained representation candidate after actual combined Lean gates."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-EXPECTATION-MIGRATION-20261005'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as handle:
  if isinstance(x,str):handle.write(x.rstrip('\n')+'\n')
  else:json.dump(x,handle,ensure_ascii=False,indent=2);handle.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineExpectation.lean')
assert load(run/'body-binding-audit-v1.json')['status']=='passed'
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineExpectation.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(label+'.log')).read_text(encoding='utf-8'));assert m,label
 jobs[label]=int(m.group(1))
ready=load(run/'ready-dependencies-v1.json');assert sha(ready['graph_path'])==ready['graph_sha256']
write('compiled-dependencies-v1.json',dict(status='fresh-scoped-actual-compiled-graph-with-unchanged-definition-proof-tokens',**{k:ready[k] for k in ['graph_path','graph_sha256','scope_nodes','actual_edges','project_proof_pairs','new_export','full_graph_export','canary_graph_export']},qualified_module_only_comment_delta=True,current_code_tokens_identical=True,fresh_root_Tests_jobs=jobs,teaching_edges_are_not_proof_dependencies=True))
write('memory-digest-candidate-v1.md','Seven retained representation proofs/three unchanged definitions/zero new code/nodes. Distinct contract/body accepted-with-explicit-delta;6reader corrections applied. Arbitrary measure/unnormalized total lower integrals/EReal difference versus legitimate signed-integral meaning; both infinite formalbottom excluded. Real Integrable explicit, AE nonnegative formal reduction, infinite-positive requires finite negative. TwoAtoms mass2/count infinite not probability Jensen canaries; parentJensen/negative-part producer distinct revalidation remains.18named standard3-or-none axioms/10native guards/fullbyteexactcanary, scoped10node317edge actualgraph. Root/Tests passed, fullharness/site/registry/finalreader/contributor/PR pending. WholeGoalACTIVE/Chapter2null/incomplete/legacy17beforepackage/globalSGB unchanged.')
write('retrieval-index-candidate-v1.md','Frozen10headers/full3definitioncontext:online-expectation-migration-v1; public OnlineExpectation positiveIntegral/negativeIntegral/signedExpectation and7helpers. Wholecanary6proofs2defs/18namedaxioms/10guards; actualpinned Bochner/lintegral/EReal APIs and scopedcompiled10nodes317directedges. Separate contract/body receipts and snapshots; same shared Bookregistry and4representativelinks. No source Theorem2.9 acceptance or new mathproofs.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=7,retained_definitions=3,new_proofs=0,frozen_headers=freeze['headers'],fresh_jobs=jobs,remaining_gates=['fullharness','contributor','site/registry/finalreader','raw/PR'],parent_accepted=False,chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only retained representation foundations candidate, Jensen/Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'signedExpectation_coe_integrable'),'--declaration','BanditRL.OnlineConvex.signedExpectation_coe_integrable','--file',public.as_posix(),'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineConvex.positiveIntegral_coe_ne_top:compiled','--dependency','lean:BanditRL.OnlineConvex.negativeIntegral_coe_ne_top:compiled','--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Retained representation candidate/currentgraph/combinedrootTests/task-onlyfrontier recorded; package pending.')
