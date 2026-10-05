"""Record the four retained minorant dependencies after actual combined Lean gates."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-MINORANT-MIGRATION-20261005'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))

def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')

def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineConvexMinorant.lean')
assert load(run/'body-binding-audit-v1.json')['status']=='passed'
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineConvexMinorant.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(label+'.log')).read_text(encoding='utf-8'));assert m,label
 jobs[label]=int(m.group(1))
assert load(run/'Tests-v1-01-exit.json')['started_at']>=load(run/'root-v1-01-exit.json')['ended_at']
ready=load(run/'ready-dependencies-v1.json');assert sha(ready['graph_path'])==ready['graph_sha256']
write('compiled-dependencies-v1.json',dict(status='fresh-scoped-actual-compiled-graph-with-unchanged-proof-tokens',**{k:ready[k] for k in ['graph_path','graph_sha256','scope_nodes','actual_edges','project_proof_pairs','new_export','full_graph_export','canary_graph_export']},qualified_module_only_comment_delta=True,current_code_tokens_identical=True,fresh_root_Tests_jobs=jobs,root_Tests_sequential=True,teaching_edges_are_not_proof_dependencies=True,edge_boundary='Direct type/value references, including definitions; not all theorem-to-theorem pairs.'))
ob=load(run/'proof-obligations-proving-v1.json');ob['stage']='candidate'
for row in ob['required']:row['state']='fresh-body-and-combined-Lean-passed-package-gates-pending'
write('proof-obligations-candidate-v1.json',ob)
write('memory-digest-candidate-v1.md','Four retained affine-support/minorant proofs, no production definitions/new proof code/nodes. Distinct contract/body accepted-with-explicit-delta; seven reader corrections applied. Actual finite-dimensional real normed contexts, no supplied Borel/measure/probability/CompleteSpace/inner-product classes. Genuine finite-neighbourhood helper produces global no-bottom and negative vertical separation coefficient before legal division; loss differentiability not assumed. First two support results touch f(x), last two only give a global bound; output slope may zero. Ambient interior remains in the two interior helpers. General terminal uses only no-bottom/convex real epigraph/nonempty domain and produces intrinsic affine-span interior, restricted ambient interior, linear extension/continuity/intercept. Nonclosed lower-dimensional coordinate/top-outside geometric canary has six proofs/one definition; not a probability Jensen-loss test. Eleven named standard-or-none axioms/four guards, actual scoped four-node896-edge graph, not full/canary. Sequential root/Tests passed; fullharness/site/registry/finalreader/contributor/PR pending. Whole Goal ACTIVE, Chapter2 null/incomplete, Jensen parent not accepted, legacy15 before package, global SGB unchanged.')
write('retrieval-index-candidate-v1.md','Exact four headers and actual class scopes: online-minorant-migration-v1. Public OnlineConvexMinorant finite-neighbourhood support/domain-interior support/domain-interior minorant/general convex_affine_minorant; frozen nonclosed lower-dimensional canary six proofs/one definition, eleven named axioms/four guards. Actual pinned separation/intrinsicInterior/linear-extension/Fermat APIs; compiled scoped four nodes896 direct type/value edges. Distinct contract/body receipts/raw snapshot bindings; two curated teaching links/highlights represent four public results in the same registry. Necessary source Theorem2.9 dependency, no parent acceptance or new mathematics.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=4,retained_definitions=0,new_proofs=0,frozen_headers=freeze['headers'],fresh_jobs=jobs,remaining_gates=['fullharness','contributor','site/registry/finalreader','raw/PR'],parent_accepted=False,chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only affine-minorant dependency candidate, Jensen/Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'convex_affine_minorant'),'--declaration','BanditRL.OnlineConvex.convex_affine_minorant','--file',public.as_posix(),'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineConvex.affine_support_of_finite_neighborhood:compiled','--dependency','lean:BanditRL.OnlineConvex.affine_support_of_domain_interior:compiled','--dependency','lean:BanditRL.OnlineConvex.affine_minorant_of_domain_interior:compiled','--dependency','lean:BanditRL.OnlineConvex.supporting_functional_at_closure:compiled','--dependency','lean:BanditRL.OnlineConvex.convex_effectiveDomain:compiled','--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Four retained minorant candidates and sequential root/Tests recorded; full package acceptance pending.')
