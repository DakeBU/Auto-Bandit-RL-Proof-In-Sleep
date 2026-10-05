"""Record bounded reuse candidate after separately logged combined root and Tests."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-FIRST-ORDER-MIGRATION-20261005'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
    p=run/n;assert not p.exists(),p
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineConvexFirstOrder.lean')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineConvexFirstOrder.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
    assert load(run/(label+'-exit.json'))['exit_code']==0
    m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(label+'.log')).read_text(encoding='utf-8'));assert m,label
    jobs[label]=int(m.group(1))
ready=load(run/'ready-dependencies-v1.json');assert sha(ready['graph_path'])==ready['graph_sha256']
write('compiled-dependencies-v1.json',dict(status='fresh-scoped-actual-compiled-graph-with-unchanged-proof-tokens',**{k:ready[k] for k in ['graph_path','graph_sha256','scope_nodes','actual_edges','project_proof_pairs','new_export','full_graph_export','canary_graph_export']},
    qualified_module_only_comment_delta=True,current_code_tokens_identical=True,fresh_root_Tests_jobs=jobs,teaching_edges_are_not_proof_dependencies=True))
write('memory-digest-candidate-v1.md','Three retained first-order bodies/no definitions/new proof code/registry nodes. Distinct source contract and actual body review accepted-with-explicit-delta; four reader corrections addressed. Canonical local derivative/global noBottom/ambient interior/all-y top retained. Real ConvexOn helper does not need open V or local EReal bridge; historical OGD RegularLoss stronger, separate source-compatible adapter explicit. Twelve named standard3-or-none axioms/3guards/byte-unchanged meaningful canary/current scoped3node416edge actual graph. Combined root/Tests passed, full harness/registry/site/final reader/contributor/raw/PR pending. Whole Goal active/Chapter2totalnull/legacy19 before scoped acceptance/globalSGB unchanged.')
write('retrieval-index-candidate-v1.md','Source/native3header/context contracts:docs/contracts/online-first-order-migration-v1. Public OnlineConvexFirstOrder/theorem_2_7/local finitePart/real ConvexOn helper; unchanged Tests.OnlineConvexFirstOrderCanary. Actual types/gradient/EReal API retrieval/12namedaxioms/3nativeguards; fresh scoped compiled3node416edge graph and actual value pairs. Separate contract/body receipts, historical raw snapshots. Same shared registry/Book route; whole chapter/book incomplete.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=3,new_proofs=0,frozen_headers=freeze['headers'],fresh_jobs=jobs,remaining_gates=['full harness','contributor','site/registry/final reader','raw binding/PR'],chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only retained Theorem2.7 chain candidate, Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'theorem_2_7'),'--declaration','BanditRL.OnlineConvex.theorem_2_7','--file',public.as_posix(),'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineConvex.finitePart_eventually:compiled','--dependency','lean:BanditRL.OnlineConvex.convex_gradient_lower_bound:compiled','--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Retained3body reuse candidate, current scoped graph/root/Tests and task-only frontier/shadow recorded.')
