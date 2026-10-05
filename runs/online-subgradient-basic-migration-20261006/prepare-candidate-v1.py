"""Candidate after actual sequential combined builds; scoped frontier only."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-BASIC-MIGRATION-20261006'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineSubgradientBasic.lean')
assert load(run/'body-binding-audit-v1.json')['status']=='passed'
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineSubgradientBasic.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
for p,h in dict(freeze['canary'],**freeze['root_Tests']).items():assert sha(p)==h,p
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
assert load(run/'Tests-v1-01-exit.json')['started_at']>=load(run/'root-v1-01-exit.json')['ended_at']
ready=load(run/'ready-dependencies-v1.json');assert sha(ready['graph_path'])==ready['graph_sha256']
write('compiled-dependencies-v1.json',dict(status='fresh-scoped-compiled-environment-graph-with-unchanged-mathematical-tokens',**{k:ready[k] for k in ['graph_path','graph_sha256','nodes','proof_nodes','definition_nodes','edges','required_proof_value_pairs','actual_project_value_pairs','full_graph_export','canary_graph_export','no_proof_value_edges_between_two_terminals']},qualified_module_only_comment_delta=True,current_code_tokens_identical=True,fresh_root_Tests_jobs=jobs,root_Tests_sequential=True,teaching_edges_are_not_proof_dependencies=True))
ob=load(run/'proof-obligations-proving-v1.json');ob['stage']='candidate'
for row in ob['required']:row['state']='fresh-body-and-combined-Lean-passed-package-gates-pending'
write('proof-obligations-candidate-v1.json',ob)
digest='Definition2.20 proper-source/generic-allEReal wider specialization and required unnumbered domain observation/T2.21;2retainedproof1complete definition/0newmathcode,nodes. Initial00sourceproperness prose corrected beforestabilization via00contextv2/audit. Propernessfiniteglobalwitness producespointdomain, convexity sourcepremise dropped in stronger actual; exact universal conversion yields domsubdiffsubsetdomain/outsideemptiness. T2.21 globallyREALf/ConvexV/globalALLambienty supportexistence sourcehypothesis; actual weighted supportsincl0/1 cancelinnerterms produceConvexOn, no suppliedtargetconvexity. Arbitraryrealinnerproduct/ambientnonemptyzero/Vempty allowed, no Complete/FiniteD. Whole3genuinecanaries/6namedstandard3-or-none axes/no sorryAx/2guards/3nodes320directreferences inclcompleteS/no mutual2proofedges. FreshdistinctCONTRACT/BODY and selectedreaderqualifications/sequentialcombinedrootTests passed. Fullharness/contributor/site/history/finalreader/PRpending.0newproofgain/legacy9->8ONLYOnlineSubgradientBasic aftergatesPR; sourceinterior+relativeinteriorfootnote/T2.22/T2.23mandatoryseparate. Chapter1migration/Chapter2null/incomplete/wholeGoalACTIVEunbudgeted/mainliveSGBunchanged. Three distinctautomatedactors requestedAstra medium/nohumanexternalruntimeattestation; commandforced vsfilepromptconventions distinct. Globalindexrewrite notrun, scopedretrievalfresh.'
write('memory-digest-candidate-v1.md',digest)
write('retrieval-index-candidate-v1.md','Exact2nativeheaders/complete support definition/actual6@types; actual SourceProper/effectiveDomain/ConvexOn/inner_sub_right/real_inner_smul_right/EReal finitecoercion APIs. Fresh3nodes320directcompiledreferences/no mutual2proofvalueedges; unchanged3genuinecanaries. Correctedsourcepropernessv2/blind/CONTRACT/BODY/rawhistory.0newmath/imports/dependencies; scopedretrieval fresh/globalindexrewrite notrun/packagepending/Chapter2Bookincomplete.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=2,retained_definitions=1,new_proofs=0,frozen_headers=freeze['headers'],fresh_jobs=jobs,remaining_gates=['fullharness','contributor','site/registry/finalreader','raw/PR'],source_terminal_accepted=False,chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only subgradient-basic candidate, Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'theorem_2_21'),'--declaration','BanditRL.OnlineConvex.theorem_2_21','--file',public.as_posix(),'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineConvex.SourceSubdifferential:compiled','--dependency','lean:BanditRL.OnlineConvex.SourceProper:compiled','--dependency','lean:BanditRL.OnlineConvex.extendedIndicator:compiled','--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Candidate/sequentialrootTests/task-only frontier recorded; integrated acceptance pending.')
