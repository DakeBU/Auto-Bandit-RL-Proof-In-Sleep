"""Record the exact source Jensen candidate after authoritative sequential combined builds."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-JENSEN-MIGRATION-20261005'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))

def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')

def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineJensen.lean')
assert load(run/'body-binding-audit-v1.json')['status']=='passed'
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineJensen.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(label+'.log')).read_text(encoding='utf-8'));assert m,label
 jobs[label]=int(m.group(1))
assert load(run/'Tests-v1-01-exit.json')['started_at']>=load(run/'root-v1-01-exit.json')['ended_at']
ready=load(run/'ready-dependencies-v1.json');assert sha(ready['graph_path'])==ready['graph_sha256']
write('compiled-dependencies-v1.json',dict(status='fresh-scoped-actual-compiled-graph-with-unchanged-proof-tokens',**{k:ready[k] for k in ['graph_path','graph_sha256','scope_nodes','actual_edges','project_proof_pairs','new_export','full_graph_export','canary_graph_export']},qualified_module_only_comment_delta=True,current_code_tokens_identical=True,fresh_root_Tests_jobs=jobs,root_Tests_sequential=True,teaching_edges_are_not_proof_dependencies=True,edge_boundary='Direct type/value references include definitions, not all theorem-to-theorem pairs.'))
ob=load(run/'proof-obligations-proving-v1.json');ob['stage']='candidate'
for row in ob['required']:row['state']='fresh-body-and-combined-Lean-passed-package-gates-pending'
write('proof-obligations-candidate-v1.json',ob)
write('memory-digest-candidate-v1.md','One source Theorem2.9 plus genuine negative-part producer, two retained proofs/no production definitions/new proof code/nodes. Distinct contract/body accepted-with-explicit-delta; seven reader corrections applied. Explicit ordinary finite Lebesgue coordinate mean corresponds to finiteD genuine Bochner Integrable, excludes principal-value/nonintegrable-zero fallback. Actual finiteD realnormed measurable/Borel E/probability1/global no-bottom/measurableconvexf/measurableIntegrableX/AEdomain; no supplied lossIntegrable/closed/lsc/fullDimension/finiteSupport/terminal oracle. Actual integrable affine lower bound produces finite negative; infinite positive yields legitimate top, finite parts produce actual measurable AEreal IntegrableY/original nonclosed epigraph mean and signed-real equality. Whole canary13proofs3defs2probinstances normalized finite nonconstant, geometric integrable input/infinite square, nonclosed lowerdimloss. Twenty actual named standard-or-none axioms v2 includes both true instance names; failed guesses v1 preserved, native repair→proving, no math/test repair. Two guards/actual scoped2nodes350directedges not full/canary. Sequential root/Tests passed; fullharness/site/registry/finalreader/contributor/PR pending. Legacy14beforepackage, Chapter2null/incomplete, GoalACTIVE/globalSGBunchanged.')
write('retrieval-index-candidate-v1.md','Exact two source/producer headers and common contexts in online-jensen-migration-v1; finite-mean interpretation contract-reviewed. Public OnlineJensen and bytefixed three probability canary routes13proofs3defs2actualinstances/20namedaxesv2/2guards. Pinned integrable_pi_iff/PiLp, real finite-part integrability/global integral_pair, accepted minorant/original nonclosed barycenter/signed compatibility; scoped2nodes350direct type/value edges. Initial API namespace and named-instance lookup failures preserved; global reference-index not refreshed, read-only retrieval/current environment fresh. Distinct contract/body/source-blind-current-packet receipts/history raw snapshots; same two shared registry nodes/source-qualified links. Source package pending, chapter/book incomplete, zero new proof code.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=2,retained_definitions=0,new_proofs=0,frozen_headers=freeze['headers'],fresh_jobs=jobs,remaining_gates=['fullharness','contributor','site/registry/finalreader','raw/PR'],source_terminal_accepted=False,chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only source Jensen/negative-part candidate, Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'theorem_2_9'),'--declaration','BanditRL.OnlineConvex.theorem_2_9','--file',public.as_posix(),'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineConvex.jensen_negativeIntegral_ne_top:compiled','--dependency','lean:BanditRL.OnlineConvex.convex_affine_minorant:compiled','--dependency','lean:BanditRL.OnlineConvex.integral_mem_convex_finiteDimensional:compiled','--dependency','lean:BanditRL.OnlineConvex.signedExpectation_eq_top:compiled','--dependency','lean:BanditRL.OnlineConvex.signedExpectation_coe_integrable:compiled','--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Exact source Jensen candidate and sequential root/Tests recorded; full package acceptance pending.')
