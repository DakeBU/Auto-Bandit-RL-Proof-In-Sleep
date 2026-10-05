"""Apply seven reviewed qualifications, retaining all mathematical source bytes."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-CLOSED-PROPER-MIGRATION-20261006'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x,existing=False):
 p=Path(p);assert p.exists() if existing else not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
r=load(run/'public-body-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r.get('mathematical_repairs',r.get('required_mathematical_repairs',[])) and sha(r['report'])==r['report_sha256']
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
for row in load(run/'public-body-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256'],row['path']
for p,h in reviewed.items():assert sha(p)==h,p
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=r['report_sha256'],retained_proofs=3,retained_definitions=2,new_proofs=0,required_reader_corrections=r.get('required_reader_corrections',[])))
snap={row['path']:row for row in load(run/'historical-raw-supersession-v1.json')['rows']}
for p in ['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:assert sha(p)==snap[p]['raw_sha256']==sha(snap[p]['snapshot']),p
public=Path('BanditRLProof/OnlineClosedProper.lean');original=(run/'original-OnlineClosedProper.lean.txt').read_bytes();assert public.read_bytes()==original
comment='''/-
Orabona v10, printed16/PDF28: Definitions2.16/2.18, Examples2.17/2.19,
and the required unnumbered closedness/lower-semicontinuity equivalence.
Three retained proofs and two complete definitions; zero new math code/nodes.
The source gives Euclidean and more generally Hausdorff sufficient scope;
actual arbitrary topological scope is a stronger generalization, no T2 premise.
SourceClosed uses REAL cuts; the proof derives bottom strict superlevels by
the union of real cuts, handles top by empty, and admits both infinite values.
No convexity/properness/no-bottom or closed-epigraph replacement is assumed.
SourceProper itself has no topology binder; the ACTUAL proper-indicator iff
still retains TopologicalSpace E. No Nonempty E or closed/convex V premise.
The SAME canonical zero-on-V/top-outside extendedIndicator is reused.
Direct indicator cuts and genuine finite witnesses prove the two indicator
equivalences independently; reading order is not a theorem dependency chain.
Empty ambient: closedness vacuous, properness false. Full indicator properness
is exactly ambient nonemptiness. Bottom-improper examples use the real line.
Whole six canary proofs and all eleven named axiom checks include bottom_closed.
All original headers/proof/definition bytes and whole canary remain fixed.
Chapter2 and the persistent Chapters1-16 Goal remain incomplete.
-/
'''
public.write_bytes(comment.encode('utf-8')+original)
write(run/'public-comment-qualification-v1.json',dict(path=public.as_posix(),original_sha256=hashlib.sha256(original).hexdigest(),qualified_sha256=sha(public),delta='leading ordinary ignored source/scope comment only',exact_original_bytes_retained_as_suffix=True))
p=Path('website/content/readings.json');d=load(p);x=next(row for row in d['readings'] if row['slug']=='online-closed-proper')
x['primary']['sections']='Section2.2.1, Definitions2.16/2.18, Examples2.17/2.19 and required unnumbered closedness/LSC equivalence; four numbered anchors, three retained proofs and two definitions'
x['notation'][0]['meaning']='SourceClosed(f) means every REAL-r sublevel is closed. Values include both infinities. Actual [TopologicalSpace E] suffices; source Euclidean/more generally Hausdorff scope is generalized, no T2 needed.'
x['notation'][1]['meaning']='SourceProper(f) is nowhere bottom AND an actual point with finite-real value. The definition has no topology binder; actual proper-indicator iff retains [TopologicalSpace E]. No Nonempty E is assumed.'
x['notation'][2]['meaning']='The SAME canonical extendedIndicator is0 on V/top outside, distinct from ordinary Set.indicator. No closed/convex/nonempty premise on V to state either iff.'
assert len(x['source_theorems'])==3 and len(x['teaching_route'])==3
for i,card in enumerate(x['source_theorems']):
 card['relationship']='Four numbered anchors comprise two definitions and two indicator examples, plus one REQUIRED unnumbered LSC equivalence. Three retained proofs/two full definitions/zero new math code or nodes. Source Euclidean and stated Hausdorff sufficient scope specialize actual arbitrary-topological scope, a stronger generalization. Reading order is not a proof dependency chain.'
 card['contract']['regret']='Foundational definitions/equivalences, no regret or subgradient guarantee.'
 card['local_status']['label']='Retained closed/proper bodies, freshly checked'
 card['local_status']['boundary']='Distinct CONTRACT/BODY, complete11namedaxes/3nativeguards and whole6canaries checked separately from combined/root/Tests/harness/site/finalreader/PR. Not Chapter2 completion; mandatory total null/incomplete and whole-book Goal active.'
 if i==0:
  card['contract']['model']='EReal-valued function on arbitrary topological E; source Euclidean and stated Hausdorff domains are included.'
  card['contract']['assumptions']='Only TopologicalSpace E. No T2/Hausdorff, convexity, properness, no-bottom, finite dimension or nonempty ambient premise. No closed-effective-domain or closed-epigraph substitute.'
  card['contract']['parameters']='SourceClosed quantifies REAL thresholds. LSC covers all EReal thresholds: bottom strict superlevel is the real-density union, finite cuts by complements, top empty.'
 elif i==1:
  card['contract']['model']='Same canonical zero-on-V/top-outside extendedIndicator on arbitrary topological E.'
  card['contract']['assumptions']='Only TopologicalSpace E; all V, including empty/full/nonclosed/nonconvex. Neither Vclosed nor Vnonempty is assumed for the iff.'
  card['contract']['parameters']='Direct real-r cuts equal V if r>=0 and empty if r<0; r0 yields necessity. No call to the preceding LSC theorem.'
 else:
  card['contract']['model']='Same canonical indicator; SourceProper itself applies to every type without topology, while this actual iff has TopologicalSpace E.'
  card['contract']['assumptions']='No Nonempty E, closed/convex V or Vnonempty premise. Finite-somewhere and nowhere-bottom are both required.'
  card['contract']['parameters']='A finite indicator value forces membership; a member witnesses value0 and nowhere-bottom. Empty E has no proper functions; full indicator proper iff E nonempty.'
x['proof_bridge']['summary']='Three independently ready retained equivalences share complete definitions and the canonical indicator. The teaching order does not assert theorem-to-theorem proof edges.'
x['proof_bridge']['steps'][0]['detail']='Complement finite real cuts. EReal.exists_between_coe_real makes the bottom strict superlevel a union of real strict superlevels; top is empty. Reverse direction uses actual closed preimages. No bottom exclusion/properness/convexity/T2 premise.'
x['proof_bridge']['steps'][1]['detail']='Calculate the canonical indicator real cut directly: V if r>=0, empty otherwise. Cut0 proves necessity and all exact cuts give sufficiency. This proof does not call the preceding LSC theorem.'
x['proof_bridge']['steps'][2]['detail']='A finite indicator value forces a point of V; a member gives value0 and nowhere-bottom. SourceProper core has no topology, although actual properiff keeps [TopologicalSpace E]. No closed/convex/nonempty ambient assumption.'
x['proof_bridge']['boundary']='Source Euclidean/more generally Hausdorff sufficient scope is strengthened to arbitrary topology. Source sublevel closedness is not a proved epigraph-closure equivalence. Actual5scopednodes213direct type/value references include2definitions, not full/canary export; no mutual theorem value edges between3proofs. Same10809registryIDsURLs expected/0new. No subgradient theorem or Chapter2 completion.'
x['worked_example']['steps'][0]['detail']='On the REAL line, constant bottom has every real sublevel full, is closed/LSC, and fails nowhere-bottom. Empty ambient is different: all functions closed but none proper since no finite witness.'
x['worked_example']['steps'][1]['detail']='The genuinely nonconstant canonical zero/top indicator of real[0,1] is closed/proper, with member0. The full indicator on arbitrary E is proper exactly when E is nonempty.'
x['worked_example']['boundary']='Whole unchanged6proof canary: bottom closed/LSC/improper, nonconstant real interval indicator closed/proper, empty indicator improper. All11namedaxes include bottom_closed omitted by old print list;3nativeguards are separate from compilation. Empty ambient/full-set boundaries follow public statements, not additional claimed canary tests. No convexity/subgradient-existence result.'
x['algorithm']['steps'][0]['detail']='Real-cut complements plus actual real density derive bottom strict superlevel; top empty. Includes bottom-valued losses on arbitrary topology.'
x['algorithm']['steps'][1]['detail']='Calculate indicator cuts independently of the LSC theorem, without any convexity or properness premise.'
x['algorithm']['steps'][2]['detail']='Finite witness and nowhere-bottom are distinct. Empty ambient has no witness; actual properiff topology binder is API context, not a mathematical properness condition.'
write(p,d,True)
p=Path('website/content/highlights.json');d=load(p)
for x in d['highlights']:
 if x.get('chapter')!='online-closed-proper':continue
 n=x['full_name'].rsplit('.',1)[-1]
 x['position']='Orabona v10 printed16/PDF28; four numbered anchors/two definitions/two examples plus REQUIRED unnumbered equivalence,3retainedproofs/0newnodes.'
 x['lean_notes']='Source Euclidean/stated Hausdorff sufficient scope specializes actual arbitrary-topological generalization, no T2/convexity/properness or Nonempty E premise. Both infinite function values/REAL cuts retained; no closed-epigraph substitute.' if n!='sourceProper_indicator_iff' else 'SourceProper core has no topology; ACTUAL public properiff retains [TopologicalSpace E]. Nowhere-bottom plus finite-somewhere; no Nonempty E/closed/convex V premise. Empty ambient has no proper function; full indicator proper iff ambient nonempty.'
 x['why']='Source-qualified prerequisite in the same shared Lean/Book registry; no new proof-count gain or Chapter2 completion.'
 if n=='sourceClosed_indicator_iff':x['proof_idea']='Direct canonical indicator cuts V if r>=0 else empty, with r0 necessity; independent of the LSC theorem.'
write(p,d,True)
p=Path('website/content/chapters.json');d=load(p);x=next(row for row in d['chapters'] if row['slug']=='online-closed-proper')
x['summary']='Real-cut closedness/LSC and proper finite witnesses for shared extended indicators, with explicit arbitrary-topological generalization.'
x['completion_definition']='Definitions2.16/2.18, Examples2.17/2.19 and REQUIRED unnumbered closedness/LSC equivalence:3retainedproofs2full definitions/0newmathcode,nodes; not Chapter2 completion.'
x['completion_blockers']=['Other mandatory Chapter2 main-text/necessary appendix source matching and legacy migrations remain required; some already have compiled bodies, so not uniformly unproved.','Chapter1 migration incomplete; Chapter2 mandatory total null/incomplete, Chapters3–16 mandatory unenumerated and whole-book Goal active.']
x['learning_goals']=['Separate REAL cuts from infinite function values and derive the bottom threshold.','Read source Euclidean/Hausdorff scope as a specialization of the stronger arbitrary-topological Lean result.','Distinguish topology-free properness definition from actual topology-bearing public iff.','Use the same zero/top indicator, genuine finite witnesses and empty ambient/set boundaries; teaching order is not proof dependency.']
x['open_gaps']=['Remaining mandatory Chapter2 main-text/appendix/legacy source migrations must be revalidated, including already compiled but unaudited subgradient statements; no Chapter3 proof competition.']
write(p,d,True)
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
 old=load(snap[p]['snapshot']);new=load(p)
 assert [row for row in old[k] if row.get(key)!='online-closed-proper']==[row for row in new[k] if row.get(key)!='online-closed-proper'],p
 for extra in set(old)-{k}:assert old[extra]==new[extra]
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert public.read_bytes().endswith(original) and tokens(public.read_text(encoding='utf-8'))==tokens(original.decode('utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
for p,h in dict(freeze['canary'],**freeze['root_Tests']).items():assert sha(p)==h,p
paths=[public.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json'];named=load(run/'public-named-declarations-v1.json');names=named['public_proofs']+named['public_definitions']
c=load('research-wiki/contribution-contracts/online-huber-migration-20261006.json')
c.update(id=task,frontier_cell='online-closed-proper',target='Distinct source/retained-body integration of four numbered anchors and required unnumbered equivalence,3proofs2full definitions/0newmathcode; seven reader qualifications, mathematical source/canary/rootTests fixed.',affected_files=paths,declarations=names)
c['source']['anchor']='Definitions2.16/2.18, Examples2.17/2.19 plus required unnumbered closedness/LSC equivalence; printed16/PDF28.'
c['reuse_plan']=dict(classification='reuse',decision='reuse_existing',searched_existing=['Fresh actual3headers/2full definitions/11@types/pinned topology/EReal APIs/current5node213edge compiled scope.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['Tests.OnlineClosedProperCanary'],planned_consumers=['Remaining mandatory Chapter2 subgradient source matching after this package gates.'],no_duplicate_wrapper=True,decision_reason='Retained realcuts/LSC/indicator/properness bodies and same canonical shared indicator,0newmathcode/nodes.')
delta='Explicit source Euclidean/stated Hausdorff sufficient scope to stronger arbitrary topology; SourceProper core topology-free but actual properiff retains TopologicalSpace. Real cuts/both infinities/no no-bottom-properness-convexity premises; emptyambient/empty/full sets and finite witness. Three independent proofs, no mutual value edges; four numbered anchors+required unnumbered result,3retainedproofs2complete definitions/0newnodes.'
c['semantic_roundtrip'].update(status='accepted',verdict=r['verdict'],remaining_semantic_delta=delta+' Distinct CONTRACT/BODY accepted; corrected reader/final package pending. Three automated actors/nohumanexternalruntimeattestation.')
c['graph_contribution'].update(lean_graph='reuse-only',focus_targets=names,functor_reason='Source-qualified same shared registry reuse, no separately certified setting functor or discovery claim.',visual_review='Actual5scopednodes213direct type/value edges/2defs, no mutual edges among3proofs; notfull/canaryexport.10809oldIDsURLs/0newexpected, sitepending.')
c['progress_updates'].update(teaching_route='Same online-closed-proper three links/highlights; seven separately reviewed qualifications, reading order not proof dependency.',website_surfaces=paths[1:])
c['truth_boundary']=delta+' Whole6canaryproofs/all11namedaxes/3guards separate fromcombinedgate. RootTests/fullharness/registry/site/finalreader/PRpending, Chapter1migration/Chapter2null/incomplete/wholeGoalACTIVE/mainliveunchanged.'
c['verification'].update(focused_checks=['Fresh3proofs2full definitions/whole6canaries/11standard3-or-none axes/no sorryAx/3nativeguards; allmathtokens/wholecanary/rootTests fixed.'],owned_test_files=[],bandit_check='Fresh sequentialroot/Tests/fullharness pending.',site_build='Clean lean-verified local build only after applicable fresh combinedLeangate.',site_check='Same5canonicalnodes/all10809IDsURLs/0newexpected/source-qualified reader pending.')
write('research-wiki/contribution-contracts/online-closed-proper-migration-20261006.json',c)
write(run/'reader-integration-v1.json',dict(status='integrated-package-pending',affected_files=paths,selected_route='online-closed-proper',required_reader_corrections_addressed=True,all_other_Book_subtrees_unchanged=True,all_headers_proof_definition_tokens_canary_root_Tests_preserved=True,retained_proofs=3,retained_definitions=2,new_proofs=0,new_registry_nodes=0,source_terminal_accepted=False,chapter_complete=False,goal_complete=False))
with Path('MANIFEST.md').open('a',encoding='utf-8',newline='\n') as f:f.write('\n- Closed/proper migration20261006: four numbered anchors plus required unnumbered equivalence/3retained proofs2complete definitions/0newmathcode,nodes; realcuts/both infinities/arbitrary-topological generalization/actual topologybinder/shared indicator/finite witness/emptyambient. Distinct CONTRACT/BODY, seven reader qualifications/all11axes3guards; integrated/finalreader/PR pending, Chapter2/Book incomplete. See runs/online-closed-proper-migration-20261006.\n')
print('Seven selected-reader qualifications applied; all mathematical bytes retained as suffix, other Books unchanged.')
