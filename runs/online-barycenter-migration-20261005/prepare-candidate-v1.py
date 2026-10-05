"""Record exact retained barycenter candidate after actual combined Lean gates."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-BARYCENTER-MIGRATION-20261005'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineConvexBarycenter.lean')
assert load(run/'body-binding-audit-v1.json')['status']=='passed'
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineConvexBarycenter.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(label+'.log')).read_text(encoding='utf-8'));assert m,label
 jobs[label]=int(m.group(1))
ready=load(run/'ready-dependencies-v1.json');assert sha(ready['graph_path'])==ready['graph_sha256']
write('compiled-dependencies-v1.json',dict(status='fresh-scoped-actual-compiled-graph-with-unchanged-proof-tokens',**{k:ready[k] for k in ['graph_path','graph_sha256','scope_nodes','actual_edges','project_proof_pairs','new_export','full_graph_export','canary_graph_export']},qualified_module_only_comment_delta=True,current_code_tokens_identical=True,fresh_root_Tests_jobs=jobs,teaching_edges_are_not_proof_dependencies=True))
ob=load(run/'proof-obligations-proving-v1.json');ob['stage']='candidate'
for row in ob['required']:row['state']='fresh-body-and-combined-Lean-passed-package-gates-pending'
write('proof-obligations-candidate-v1.json',ob)
write('memory-digest-candidate-v1.md','Only3retained barycenter/support proofs/no definitions/newcode/nodes. Distinctcontract/body accepted-with-explicit-delta;5reader corrections applied. Complete normed equality supplieda mayzero/AEfunctional VALUES notXconstant; geometricfiniteDimambientnon-strict support at a(x), no measure/strictnormalization; actualfiniteDimBorel probabilityIntegrable/AE actualsetmembership, no closedness/fullinterior/finite-support assumption. Genuine proper-kernel representative integrability/zero mean/rank descent/stronginduction produced. Meaningful bytefixed3defs7proofs1probinstance canary halfdirac1/3 nonconstant lowerdim nonclosedray mean(2,0).14namedstandard3-or-none axioms/3nativeguards, scoped3node544edge actualgraph notfull/canary. Root/Tests passed; fullharness/site/registry/finalreader/contributor/PR pending. WholeGoalACTIVE/Chapter2null/incomplete/Jensennotaccepted/legacy16beforepackage/globalSGBunchanged.')
write('retrieval-index-candidate-v1.md','Exact3headers/separatecontexts/types:online-barycenter-migration-v1. PublicOnlineConvexBarycenter supportequal/supportatclosure/actualfiniteDimconvexsetintegral; whole probabilityraycanary3defs7proofs1instance/14namedaxioms3guards. Pinned closedConvexintegral/ambientHB/AEintegralequality/CLmapintegral/finrank APIs; scoped3nodes544directedges. Distinctcontract/body/rawsnapshotbindings; sameBookregistry3links/highlights. Not3printedresults or sourceJensenacceptance; no newmathproofcode.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=3,retained_definitions=0,new_proofs=0,frozen_headers=freeze['headers'],fresh_jobs=jobs,remaining_gates=['fullharness','contributor','site/registry/finalreader','raw/PR'],parent_accepted=False,chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only nonclosed barycenter dependency candidate, Jensen/Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'integral_mem_convex_finiteDimensional'),'--declaration','BanditRL.OnlineConvex.integral_mem_convex_finiteDimensional','--file',public.as_posix(),'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineConvex.supporting_functional_ae_eq_mean:compiled','--dependency','lean:BanditRL.OnlineConvex.supporting_functional_at_closure:compiled','--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Exact retained barycenter candidate/current scopedgraph/combinedrootTests/taskfrontier recorded; package pending.')
