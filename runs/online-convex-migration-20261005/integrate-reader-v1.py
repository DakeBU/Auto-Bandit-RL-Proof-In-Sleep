"""Integrate separately reviewed convex semantics with no Lean code change."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
receipt=load(run/'public-body-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert receipt['actor']['task']=='/root/source_reviewer'
assert receipt['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not receipt.get('mathematical_repairs',receipt.get('required_mathematical_repairs',[]))
assert sha(receipt['report'])==receipt['report_sha256']
reviewed={r['path']:r['sha256'] for r in receipt['reviewed_files']}
for p,h in reviewed.items():assert sha(p)==h,p
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=receipt['report_sha256'],actual_proofs=22,
    canary_modules=4,actual_named_axioms=53,new_proofs=0,required_reader_corrections=receipt.get('required_reader_corrections',[])))
paths=list(freeze['modules'])+['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
snapshots=[]
for p in paths:
    snapshot=run/'leaves'/('pre-integration-'+p.replace('/','--')+'.txt')
    assert not snapshot.exists(),snapshot
    snapshot.write_bytes(Path(p).read_bytes())
    assert sha(snapshot)==reviewed[p],p
    snapshots.append(dict(path=p,snapshot=snapshot.as_posix(),raw_sha256=sha(snapshot),authorized_delta='source-qualified comment only' if p.endswith('.lean') else 'only online-convex and online-convex-closures subtrees'))
write(run/'historical-raw-supersession-v1.json',dict(status='exact originals preserved before source-qualified integration',rows=snapshots,prior_accepted_OGD_FTL_artifacts_not_rewritten=True))
comments={
'OnlineConvexExtended':'''Source: Orabona, Online Learning, arXiv:1912.13213v10, Definitions 2.2-2.3,
Theorem 2.4 and intervening domain/indicator consequences; printed pp.9-10,
PDF pp.21-22. General epigraph convexity uses real heights and permits both
infinities; effectiveDomain includes bottom. Empty sets/domains are allowed.
Theorem 2.4 separately retains noBottom, convex effective domain, domain points
and strictly interior real weights. Ordinary indicator addition retains its
printed noBottom premise. Proved toReal bridges do not identify infinite values
with zero. Abstract real modules include the source Euclidean instances.
The migration preserves every existing definition, header and proof token.''',
'OnlineConvexExamples':'''Source: Orabona v10, Examples 2.5 and 2.6, printed p.10 / PDF p.22.
Every affine inner-product function and every norm is convex under the shared
real-height extended-real epigraph definition. Example 2.6 remains mandatory
main text although its proof is left as an exercise. The finite coercion iff
is a library bridge, not another numbered source theorem. General real normed
and inner-product spaces include the source finite-dimensional instances.
No boundedness or nonzero slope/value assumption. Existing code is preserved.''',
'OnlineConvexClosures':'''Source: Orabona v10, three unnumbered closure bullets, printed p.10 / PDF p.22.
Affine precomposition and arbitrary indexed suprema permit both infinities,
empty domains, noninjective maps and empty index types. Monotone composition
keeps globally REAL-valued f and g and globally nondecreasing g, as printed;
it does not extend g to infinite inputs. Real-module generality includes the
source Euclidean spaces. The fourth, weighted-sum bullet uses the explicit
operation in OnlineConvexSums. All existing proof/definition code is preserved.''',
'OnlineConvexSums':'''Source: Orabona v10, nonnegative-combination bullet, printed p.10 / PDF p.22.
Orabona does not print a mixed-infinity addition convention. This module
explicitly interprets that bullet with Rockafellar's top-dominant convex-sum
convention (Conjugate Duality and Optimization, printed p.6 / PDF p.17).
upperAdd is a named operation, not ordinary mathlib EReal addition. The latter
has a public nonconvex-sum counterexample. Both infinities, improper/disjoint
domains, zero weights and EReal zero-times-infinity=zero remain included.
Finite-height witness/scaling laws are supporting refinements. The convention
is attributed interpretation, not literal Orabona text. Existing code is preserved.'''}
token=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
for group,names in freeze['groups'].items():
    p=Path('BanditRLProof')/(group+'.lean');raw=p.read_bytes()
    assert sha(p)==freeze['modules'][p.as_posix()]
    p.write_bytes(('/-\n'+comments[group]+'\n-/\n').replace('\n','\r\n').encode('utf-8')+raw)
    assert token(raw.decode('utf-8'))==token(p.read_text(encoding='utf-8')),p
    for n in names:assert hashlib.sha256(lean_declaration_header(p,n).encode()).hexdigest()==freeze['headers'][n],n
for p,h in freeze['canaries'].items():assert sha(p)==h,p
p=Path('website/content/readings.json');data=load(p)
r=next(x for x in data['readings'] if x['slug']=='online-convex')
r['source_theorems'][0]['relationship']='The shared theorem_2_4 keeps no negative infinity, convex effective domain, domain points and strict interior weights. Proved finite-value epigraph bridges reuse the real ConvexOn API; domain cardinality need not be finite.'
r['source_theorems'][1]['local_status']['boundary']='Indicator/domain consequences only. All four closure constructions have retained implementations in the same shared library; their source migration acceptance is recorded separately. Chapter2 and whole-book acceptance remain incomplete.'
r['source_theorems'][2]['relationship']='Exact shared example_2_5 and example_2_6, including the norm proof left as a main-text exercise. The real coercion iff is a library refinement; real normed/inner-product generality includes the source Euclidean instances.'
r=next(x for x in data['readings'] if x['slug']=='online-convex-closures')
r['notation'].append(dict(term='upperAdd',meaning='Named top-dominant addition -(-a+-b); ordinary EReal addition is bottom-dominant. Attributed interpretation of the unstated source convention, with zero-times-infinity=zero in scalar multiplication.'))
r['source_theorems'][0]['contract']['assumptions']='Arbitrary affine map and arbitrary index for extended-real inputs, including empty index. Composition keeps globally real-valued convex f and g and globally nondecreasing g; g is not applied to infinite values.'
r['source_theorems'][1]['relationship']='Same canonical convex_nonneg_linear_combination. Orabona leaves mixed-infinity addition unspecified; the explicit top-dominant interpretation is supported by Rockafellar, Conjugate Duality and Optimization, printed p6/PDF17, author-hosted https://sites.math.washington.edu/~rtr/papers/rtr054-ConjugateDuality.pdf (SHA256 29d57ab07857b8270c175343746c77b4138f2db6161ae20174a0bba076991b0e). The ordinary-addition counterexample is publicly tested. Current reviewed contract: docs/contracts/online-convex-migration-v1; prior sums contract remains historical.'
r['source_theorems'][1]['plain']='At mixed infinities, named upper addition returns positive infinity; the convention is an explicitly attributed interpretation and is not printed by Orabona. Ordinary mathlib EReal addition differs.'
write(p,data)
p=Path('website/content/highlights.json');data=load(p)
for n in data['highlights']:
    if n.get('chapter') not in ['online-convex','online-convex-closures']:continue
    short=n['full_name'].rsplit('.',1)[-1]
    if short=='definition_2_2':n['math']=r'\(\forall x,y\in V,\;0<\theta<1:\;\theta x+(1-\theta)y\in V\)'
    if short=='theorem_2_4':
        n['plain']='For f that never takes negative infinity and has convex effective domain, epigraph convexity is equivalent to the interior-weight inequality on domain points.'
        n['intuition']=n['plain']
        n['math']=r'\(f\text{ convex}\iff\forall x,y\in\operatorname{dom}f,\;0<\theta<1:\;f(\theta x+(1-\theta)y)\le\theta f(x)+(1-\theta)f(y)\)'
        n['lean_notes']='Explicit noBottom and convex effective domain; the domain may be unbounded, empty or infinite in cardinality. Real epigraph heights and strict interior weights; finite-value conversions are proved, not assumed.'
    if short=='convex_comp_monotone':n['lean_notes']='Globally real-valued convex f and g, with global Monotone g, exactly as printed. No extension of g to infinite values or extra convex-image premise. General real-module inputs include the source Euclidean setting.'
    if short=='convex_nonneg_linear_combination':n['lean_notes']='No noBottom, properness, common-domain or positive-only coefficient restriction. Named upperAdd uses an explicitly attributed Rockafellar convention not printed by Orabona; scalar multiplication includes zero-times-infinity=zero. Ordinary EReal addition has the public spike counterexample.'
write(p,data)
p=Path('website/content/chapters.json');data=load(p)
for c in data['chapters']:
    if c['slug']=='online-convex':c['completion_definition']='Definitions2.2-2.3, Theorem2.4 with explicit noBottom/convex effective domain and strict weights, domain/indicator consequences, and mandatory Examples2.5/2.6. Eight and three retained proofs respectively; no new proof code. This is not completion of all Chapter 2.'
    if c['slug']=='online-convex-closures':c['completion_definition']='All four p10 closure bullets, with globally real-valued monotone composition and explicitly attributed Rockafellar top-dominant upperAdd interpretation for general weighted sums. Three and eight retained proofs respectively; source helper laws are refinements. This is not completion of all Chapter 2.'
write(p,data)
names=['BanditRL.OnlineConvex.'+n for n in list(freeze['headers'])+sum(freeze['definitions'].values(),[]) ]
c=load('research-wiki/contribution-contracts/ONLINE-FTL-MIGRATION-20261005.json')
c.update(id='ONLINE-CONVEX-MIGRATION-20261005',frontier_cell='online-convex',source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',version='arXiv:1912.13213v10,21 June2026; SHA256 '+freeze['primary_sha256'],anchor='Section2.1.1; Def2.2/Def2.3/Thm2.4/Examples2.5/2.6 and unnumbered domain/indicator/four closure rules; printed9-10/PDF21-22. Explicit Rockafellar convention interpretation printed6/PDF17.',url='https://arxiv.org/pdf/1912.13213v10'),
    target='Distinctly revalidate four retained extended-convexity/example/closure production modules and correct source-qualified readers without changing proof code.',affected_files=paths,declarations=names,
    reuse_plan=dict(classification='reuse',decision='reuse_existing',searched_existing=['Actual27 public declarations/pinned mathlib APIs/compiled shared graph27nodes13 required proof-value pairs.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['Tests.'+g+'Canary' for g in freeze['groups']],planned_consumers=['Remaining Chapter2 production/source audit and later sequential chapters.'],no_duplicate_wrapper=True,decision_reason='Same22 proof bodies/five definitions reused, no new graph nodes or per-book duplicate library.'),
    semantic_roundtrip=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/normal_blind',source_reviewer='/root/source_reviewer',verdict=receipt['verdict'],remaining_semantic_delta='Distinct source-contract/body review; general real spaces, named top-dominant convention and zero-product interpretation explicit. Final corrected reader/package review pending; no human/external review.'),
    truth_boundary='Four retained modules22 proofs/five definitions, zero new proofs/registry nodes. General both-infinity epigraphs/real heights, explicit noBottom/convex-domain Thm2.4, real-valued monotone composition and named upperAdd convention not printed by Orabona. Existing canaries replayed including ordinary-sum counterexample/empty/zero/positive cases. Chapter2 mandatory_total still null; remaining historical source/migration and whole Chapters1-16 obligations not excluded. Local compilation/stacked PR do not update main/live.')
c['graph_contribution'].update(lean_graph='reuse-only',overview_graph='updated',focus_targets=names,functor_reason='Retained source convex-analysis foundations; no functor claim.',visual_review='Actual corrected reader/registry/site checks pending; teaching links distinguished from actual compiled graph.')
c['progress_updates'].update(teaching_route='updated: same two convex reader routes/ten highlights/old URLs; source hypotheses and interpretation corrected.',website_surfaces=paths[-3:])
c['verification'].update(focused_checks=['Fresh actual4 public modules/4 canary modules/53 named axioms standard3-or-none/22 actual safe guards.'],bandit_check='Fresh combined root/Tests/full harness pending.',site_build='Clean lean-verified build only after fresh applicable combined gate.',site_check='Same shared27 canonical nodes/old URLs and corrected reader validation pending.')
write('research-wiki/contribution-contracts/ONLINE-CONVEX-MIGRATION-20261005.json',c)
write(run/'reader-integration-v1.json',dict(status='integrated-pending-package-gates',affected_files=paths,selected_routes=['online-convex','online-convex-closures'],all22_headers_unchanged=True,all_Lean_code_tokens_unchanged=True,all4_canary_bytes_unchanged=True,new_proofs=0,new_registry_nodes=0,required_reader_corrections_addressed=True,final_reader_accepted=False,chapter_complete=False,goal_complete=False))
print('Reviewed convex readers/comments integrated, raw originals preserved;22 headers/all code unchanged; package gates pending.')
