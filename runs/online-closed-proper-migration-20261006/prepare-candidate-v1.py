"""Candidate after actual sequential combined builds; scoped frontier only."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-CLOSED-PROPER-MIGRATION-20261006'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineClosedProper.lean')
assert load(run/'body-binding-audit-v1.json')['status']=='passed'
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineClosedProper.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
for p,h in dict(freeze['canary'],**freeze['root_Tests']).items():assert sha(p)==h,p
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
assert load(run/'Tests-v1-01-exit.json')['started_at']>=load(run/'root-v1-01-exit.json')['ended_at']
ready=load(run/'ready-dependencies-v1.json');assert sha(ready['graph_path'])==ready['graph_sha256']
write('compiled-dependencies-v1.json',dict(status='fresh-scoped-compiled-environment-graph-with-unchanged-mathematical-tokens',**{k:ready[k] for k in ['graph_path','graph_sha256','nodes','proof_nodes','definition_nodes','edges','required_proof_value_pairs','actual_project_value_pairs','full_graph_export','canary_graph_export','no_proof_value_edges_between_three_terminals']},qualified_module_only_comment_delta=True,current_code_tokens_identical=True,fresh_root_Tests_jobs=jobs,root_Tests_sequential=True,teaching_edges_are_not_proof_dependencies=True))
ob=load(run/'proof-obligations-proving-v1.json');ob['stage']='candidate'
for row in ob['required']:row['state']='fresh-body-and-combined-Lean-passed-package-gates-pending'
write('proof-obligations-candidate-v1.json',ob)
digest='Four numbered source anchors/two definitions/two examples plus required unnumbered LSC equivalence;3retainedproofs2complete definitions/0newmathcode,nodes. SourceEuclidean/Hausdorff sufficient scope vs actual arbitrary-topological stronger generality, coreSourceProper no topology butactualproperiff retainsTopologicalSpace. REALcuts/bothinfinities/bottomrealunion/topempty/no no-bottom-proper-convex assumptions; samecanonicalindicator/directcuts/genuinefinitepoint/emptyambient-fullset. Three independent proofs/no mutual valueedges, whole6canaryproofs/all11unique standard3-or-none axes/no sorryAx/3guards, actual5nodes213directreferences includingdefs notfull/canarygraph. Distinct CONTRACT/BODY accepted/sevenreaderfixes; sequentialcombinedrootTests passed. Fullharness/contributor/site/history/finalreader/PRpending. Legacy10->9onlyOnlineClosedProperaftergates/PR;Chapter1migration/Chapter2null/incomplete/wholeGoalACTIVE/unbudgeted/mainliveSGBunchanged. Required three automated actors requestedAstra/medium/nohumanexternalruntimeattestation; CLIforced vs prompt/fileconventions distinct. Preparation failures and unused correctedhelpers retained; no mathematics/testrepair. Globalreference-index rewrite notrun, actual scopedretrieval/pinnedAPIs fresh.'
write('memory-digest-candidate-v1.md',digest)
write('retrieval-index-candidate-v1.md','Exact3nativeheaders/2complete definitions and actual11@types in online-closed-proper-migration-v1; actual pinned lowerSemicontinuous open/closed preimage and EReal.exists_between_coe_real APIs; SAMEcanonicalextendedIndicator. Fresh5nodes213directcompiledtype/value references and no mutual3proofedges; whole6genuinecanaries. Sourceblind/CONTRACT/BODY/rawhistorysnapshots; zero newgenericdeclarations/imports/dependencychanges. Scopedretrieval fresh, globalreferenceindexrewrite notrun; current packagegatespending/Chapter2Bookincomplete.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=3,retained_definitions=2,new_proofs=0,frozen_headers=freeze['headers'],fresh_jobs=jobs,remaining_gates=['fullharness','contributor','site/registry/finalreader','raw/PR'],source_terminal_accepted=False,chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only closed/proper candidate, Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'sourceClosed_iff_lowerSemicontinuous'),'--declaration','BanditRL.OnlineConvex.sourceClosed_iff_lowerSemicontinuous','--file',public.as_posix(),'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineConvex.SourceClosed:compiled','--dependency','lean:BanditRL.OnlineConvex.SourceProper:compiled','--dependency','lean:BanditRL.OnlineConvex.extendedIndicator:compiled','--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Candidate/sequentialrootTests/task-only frontier recorded; integrated acceptance pending.')
