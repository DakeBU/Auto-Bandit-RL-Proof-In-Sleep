from common_v1 import *
import base64,re
fixed()
sys.path.insert(0,str(ROOT))
from tools.bandit import scan_lean_declarations
from tools.abrl_lifecycle import lean_declaration_header,statement_hash

# Inspect actual compiler output, separately from the successful shell statuses.
build=load(RUN/'variable-focused-build-v1.json')
kernel=load(RUN/'variable-current-kernel-v1.json')
bt=base64.b64decode(build['stdout_base64']).decode('utf8')
kt=base64.b64decode(kernel['stdout_base64']).decode('utf8')
assert build['actual_exit']==kernel['actual_exit']==0
assert 'Build completed successfully (9107 jobs).' in bt
assert 'error:' not in bt and 'error:' not in kt
axioms=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",kt,re.S)
assert len(axioms)==7
for name,values in axioms:
 assert set(re.findall(r'[A-Za-z_.]+',values))=={'propext','Classical.choice','Quot.sound'},name
assert kt.count('@BanditRL.OnlineGradientDescentSource.theorem_2_13_variable')==2
write(RUN/'variable-readiness-inspected-v1.json',dict(
 scope='Actual current focused build, two complete exact-type examples, five public-value scratch witnesses, existing nondegenerate active-projection trajectory; no new production theorem or Chapter2 acceptance',
 build_receipt_sha256=sha(RUN/'variable-focused-build-v1.json'),kernel_receipt_sha256=sha(RUN/'variable-current-kernel-v1.json'),
 actual_build_success_marker='Build completed successfully (9107 jobs).',actual_axiom_records=[dict(name=n,axioms=re.findall(r'[A-Za-z_.]+',a)) for n,a in axioms],
 preserved='positive T; positive/nonincreasing finite-prefix eta; last-played eta(T-1); negative terminal distance; actual projected recurrence and gradients; source-to-feasible adapter',
 nondegenerate_canary='two rounds, decreasing rates1 then1/2, active first projection, iterate2=3/4, terminal squared norm9/16, regret1/2',
 compiler_errors=0,chapter_complete=False,book_complete=False,whole_Goal_status='ACTIVE'))

nav=load(CONTRACT/'historical-source-navigation-draft-v1.json')
groups=load(CONTRACT/'historical-unnumbered-source-audit-draft-v2.json')
source=load(CONTRACT/'source-fingerprint-v1.json')
pages={r['pdf_page']:r for r in source['source_pages']}
decls=[d for d in scan_lean_declarations() if d['file'].startswith('BanditRLProof/Online')]
by_name={d['full_name']:d for d in decls}
by_module={}
for d in decls:by_module.setdefault(Path(d['file']).stem,[]).append(d)
manifest_rows=[]
for p in sorted((ROOT/'research-wiki/contribution-contracts').glob('*.json')):
 d=json.loads(p.read_text(encoding='utf-8-sig'))
 if any('/Online' in str(x) for x in d.get('affected_files',[])):
  manifest_rows.append(dict(path=p.relative_to(ROOT).as_posix(),sha256=sha(p),id=d['id'],declarations=d.get('declarations',[]),
   affected_files=d.get('affected_files',[]),recorded_semantic_roundtrip=d.get('semantic_roundtrip',{}),recorded_verification=d.get('verification',{}),
   warning='Recorded manifest claims are not a new chapter acceptance or proof-body audit. Exact actual receipt/file bindings below are separate.'))

# Actual prior receipt -> complete current production-file matches, not status-string inheritance.
receipt_rows=[]
for folder in sorted((ROOT/'runs').glob('online-*')):
 if folder==RUN:continue
 ps=set(folder.glob('*receipt*.json'))|set(folder.glob('*decision*.json'))|set(folder.glob('*delivery*.json'))
 for p in sorted(ps):
  try:d=json.loads(p.read_text(encoding='utf-8-sig'))
  except (ValueError,UnicodeError):continue
  if not isinstance(d,dict):continue
  matches=[];mismatches=[]
  for entry in d.get('reviewed_files',[]):
   if not isinstance(entry,dict):continue
   raw=str(entry.get('path','')).replace('\\','/')
   if 'BanditRLProof/Online' not in raw:continue
   relative='BanditRLProof/Online'+raw.split('BanditRLProof/Online',1)[1]
   q=ROOT/relative
   if not q.is_file():continue
   old=entry.get('sha256');current=sha(q)
   row=dict(path=relative,recorded_sha256=old,current_sha256=current)
   (matches if old==current else mismatches).append(row)
  if matches or mismatches:
   receipt_rows.append(dict(path=p.relative_to(ROOT).as_posix(),sha256=sha(p),recorded_verdict=d.get('verdict',d.get('stage',d.get('status'))),
    recorded_scope=d.get('scope'),current_full_file_matches=matches,current_full_file_mismatches=mismatches))

declaration_rows=[]
for d in decls:
 p=ROOT/d['file'];row=dict(d)
 row['source_file_sha256']=sha(p)
 row['scope_context']='Complete immutable current module, including imports, scoped variables, definitions and actual proof BODY; header alone omits section context.'
 try:
  row['native_header']=lean_declaration_header(p,d['full_name'])
  row['native_statement_hash']=statement_hash(row['native_header'])
 except ValueError as err:
  row['native_header']=None;row['native_statement_hash']=None
  row['header_extraction_boundary']=str(err)+'; complete declaration remains bound by the full module RAW hash; no fake assignment inserted.'
 row['contribution_manifests']=[m['path'] for m in manifest_rows if d['full_name'] in m['declarations']]
 row['prior_receipts_with_matching_complete_file']=[r['path'] for r in receipt_rows if any(x['path']==d['file'] for x in r['current_full_file_matches'])]
 declaration_rows.append(row)
write(RUN/'current-online-declaration-retrieval-v1.json',dict(
 stage='actual current shared-project declaration retrieval; not independent proof-obligation denominator',
 command='tools.bandit.scan_lean_declarations(include_tests=False), native lean_declaration_header and statement_hash; RAW complete module hashes',
 base=BASE,branch=BRANCH,declaration_count=len(declaration_rows),rows=declaration_rows))
write(RUN/'prior-receipt-current-file-join-v1.json',dict(
 stage='mechanical actual provenance join; substantive seven-slot review remains separate',
 manifests=manifest_rows,receipts=receipt_rows,
 warning='A full-file match makes an earlier scoped review reusable only within its exact source/statement/canary scope. Nonmatches are retained, never silently treated as current or accepted. Earlier chapter-incomplete strings are historical, not evidence that repaired leaves remain unproved.'))

# Source containers overlap. Each row's candidate modules are implementation context,
# not a claim that every declaration in those modules directly formalizes this source object.
module_map={
 'Definition 2.2':['OnlineConvexExtended'],
 'Definition 2.3':['OnlineConvexExtended'],
 'Theorem 2.4':['OnlineConvexExtended'],
 'Example 2.5':['OnlineConvexExamples'],
 'Example 2.6':['OnlineConvexExamples'],
 'Theorem 2.7':['OnlineConvexFirstOrder'],
 'Theorem 2.8':['OnlineConvexOptimality'],
 'Theorem 2.9':['OnlineJensen','OnlineExpectation','OnlineConvexBarycenter','OnlineConvexMinorant'],
 'Algorithm 2.1':['OnlineGradientDescent','OnlineGradientDescentVariable','OnlineGradientDescentSource'],
 'Example 2.10':['OnlineFTLFailure'],
 'Proposition 2.11':['OnlineGradientDescent'],
 'Lemma 2.12':['OnlineGradientDescentSource'],
 'Theorem 2.13':['OnlineGradientDescentSource','OnlineGradientDescentVariable'],
 'Example 2.14':['OnlineGuessingOGD','OnlineGuessingLower','OnlineGuessingComparison'],
 'Example 2.15':['OnlineHuber'],
 'Definition 2.16':['OnlineClosedProper'],
 'Example 2.17':['OnlineClosedProper'],
 'Definition 2.18':['OnlineClosedProper'],
 'Example 2.19':['OnlineClosedProper'],
 'Definition 2.20':['OnlineSubgradientBasic'],
 'Theorem 2.21':['OnlineSubgradientBasic'],
 'Theorem 2.22':['OnlineSubgradientDifferentiability'],
 'Theorem 2.23':['OnlineSubgradientSum'],
 'Example 2.24':['OnlineSubgradientAbsolute'],
 'Example 2.25':['OnlineNormalCone'],
 'Theorem 2.26':['OnlineSubgradientMax'],
 'Example 2.27':['OnlineHinge'],
 'Theorem 2.28':['OnlineAffineSubgradient'],
 'Definition 2.29':['OnlineLipschitzSubgradient'],
 'Theorem 2.30':['OnlineLipschitzSubgradient'],
 'Lemma 2.31':['OnlineSubgradientDescent'],
 'Algorithm 2.2':['OnlineSubgradientPolicy','OnlineSubgradientDescent'],
 'Example 2.32':['OnlineGuessingSubgradient','OnlineGuessingSubgradientPolicy']}
primary={
 'Definition 2.2':['definition_2_2'], 'Definition 2.3':['realEpigraph','IsConvexExtended'],
 'Theorem 2.4':['theorem_2_4'], 'Example 2.5':['example_2_5'],'Example 2.6':['example_2_6'],
 'Theorem 2.7':['theorem_2_7'],'Theorem 2.8':['theorem_2_8'],'Theorem 2.9':['theorem_2_9'],
 'Algorithm 2.1':['Domain','project','step','iterate','iterateVariable','iterate_mem','iterate_prefix','iterateVariable_mem','iterateVariable_prefix','SourceRegularLoss','source_to_feasible'],
 'Example 2.10':['linearFTLPredict','linearFTLPredict_minimizes','linearFTLPredict_prefix','example_2_10'],
 'Proposition 2.11':['project_spec','proposition_2_11'], 'Lemma 2.12':['lemma_2_12'],
 'Theorem 2.13':['theorem_2_13_fixed','theorem_2_13_variable_bound','theorem_2_13_variable'],
 'Example 2.14':['example_2_14','guessing_squared_horizon_lower','guessing_vs_mean_lower','guessing_vs_mean_unbounded'],
 'Example 2.15':['huber','huber_three_pieces','huber_deriv_source','huber_linear_gradient_bound','huber_regret_fixed','huber_average_eventually'],
 'Definition 2.16':['SourceClosed'], 'Example 2.17':['sourceClosed_indicator_iff'],
 'Definition 2.18':['SourceProper'],'Example 2.19':['sourceProper_indicator_iff'],
 'Definition 2.20':['SourceSubdifferential'], 'Theorem 2.21':['theorem_2_21'],
 'Theorem 2.22':['SourceDifferentiableAt','theorem_2_22','theorem_2_22_gradient'],
 'Theorem 2.23':['SourceSubgradientSum','theorem_2_23_inclusion','theorem_2_23_equality'],
 'Example 2.24':['example_2_24'],'Example 2.25':['SourceNormalCone','indicator_subdifferential_eq_normalCone','normalCone_interior_eq_zero','normalCone_unitBall_boundary'],
 'Theorem 2.26':['SourceFiniteMax','SourceActiveSubgradientUnion','theorem_2_26'],
 'Example 2.27':['sourceHinge','example_2_27'], 'Theorem 2.28':['theorem_2_28'],
 'Definition 2.29':['SourceLipschitzOn'], 'Theorem 2.30':['theorem_2_30'],
 'Lemma 2.31':['lemma_2_31'], 'Algorithm 2.2':['OracleLaw','LegalFeedback','canonicalPolicy','canonicalPolicy_legal','history','output','selected','output_prefix','oracle_feedback','output_mem','canonical_output','canonical_selected'],
 'Example 2.32':['example_2_32_subdifferential','loss_step_clamp','guessing_prefix','example_2_32','example_2_32_average_eventually']}
signatures={
 'Definition 2.2':'Convexity of V in real Euclidean space: all x,y in V and lambda in(0,1); endpoint convention equivalent to mathlib Convex.',
 'Definition 2.3':'Convexity is convexity of the REAL epigraph of an arbitrary extended-real f; both infinities and empty effective domain permitted.',
 'Theorem 2.4':'No minus-infinity values; convex effective domain; epigraph convex iff open-segment Jensen inequality on every domain pair. Improper all-plus-infinity remains allowed.',
 'Example 2.5':'Every real affine function inner(z,x)+b is convex, with no slope or offset restriction.',
 'Example 2.6':'Every norm is convex. Main-text exercise-proof instruction does not make this optional.',
 'Theorem 2.7':'Convex extended-real f without minus-infinity, ambient differentiable at x in ordinary domain interior: global first-order support for every y, including plus-infinity values.',
 'Theorem 2.8':'Convex f and source ambient differentiability on open neighborhood of V: x* minimizes over V iff inner(gradient f x*,y-x*)>=0 for every y in V; interior-zero equivalence separately mapped.',
 'Theorem 2.9':'Proper convex extended-real f and random vector X taking finite-domain values almost surely; existing expected vector and extended signed expectation, Jensen f(E[X])<=E[f(X)]. Audit finite-dimension, measurability and negative-part integrability producers without adding finite E[f(X)].',
 'Algorithm 2.1':'Nonempty closed convex V, feasible x1; output before current loss, compute actual ambient gradient and project after feedback. Same strict-past recursive trajectory for arbitrary positive finite-prefix rates.',
 'Example 2.10':'FTL minimizes strict-past cumulative losses; any legal initial action. Explicit alternating linear losses on[-1,1] force regret T-1-x0/2, demonstrating possible linear regret.',
 'Proposition 2.11':'Projection exists on nonempty closed convex V; for EVERY ambient x and y in V, ||PiV(x)-y||<=||x-y||. Feasibility and optimality are actual producers.',
 'Lemma 2.12':'Actual projected current-gradient update gives comparator loss gap <= telescoping squared-distance term plus eta||g||^2/2. eta>0; no bounded-domain premise.',
 'Theorem 2.13':'Two distinct branches: fixed positive eta uses initial-comparator distance with no bounded V; positive nonincreasing variable eta uses finite diameter. Both retain the negative terminal squared distance and actual same-run gradients. Source1..T is Lean0..T-1.',
 'Example 2.14':'Squared guessing on[0,1], labels in[0,1], actual projected-gradient clamp update and tuned2sqrt(T) upper bound; source comparison with logarithmic FTL needs actual lower/comparison producer, not a loose-upper-bound inference.',
 'Example 2.15':'Actual Huber scalar loss and linear-feature composition; bounded features and fixed threshold give bounded actual gradients, fixed eta proportional1/sqrt(T) yields upper-epsilon average regret against each fixed linear comparator. Horizon-specific run family, real labels; no signed ordinary-limit or empirical prediction claim.',
 'Definition 2.16':'Closed extended-real f means every REAL sublevel closed, not epigraph convexity or continuity.',
 'Example 2.17':'Indicator is closed iff V is closed, permitting empty V.',
 'Definition 2.18':'Proper iff finite-valued somewhere and never minus-infinity; convexity is not part of properness.',
 'Example 2.19':'Indicator proper iff V nonempty; no closure or convexity prerequisite.',
 'Definition 2.20':'Global support at x: f(y)>=f(x)+inner(g,y-x) for ALL ambient y. Printed context proper f; generic library predicate accepts arbitrary EReal and properness is restored in source consumers.',
 'Theorem 2.21':'Every global subgradient of a proper convex f certifies x minimizes f iff0 is a subgradient. General min/support equivalence must not be narrowed to differentiable f.',
 'Theorem 2.22':'Proper convex f: ambient differentiability at x iff the FULL subdifferential is a singleton, and then it is{gradient f x}. Actual ambient real-germ differentiability, not within-domain/toReal extension semantics.',
 'Theorem 2.23':'All queried x: inclusion for finite proper components; qualified equality for convex closed proper components, positive finite family and ONE common point in last domain and all other AMBIENT interiors. Do not require all queried points interior or all components interior at witness.',
 'Example 2.24':'Full absolute-value subdifferential: singleton1 for x>0,[-1,1] at0,singleton-1 for x<0; every candidate support, not membership only.',
 'Example 2.25':'Indicator subdifferential is normal cone on V; interior cone{0}; unit-ball boundary cone all nonnegative multiples of x. Ambient query, endpoint/boundary convention explicit.',
 'Theorem 2.26':'Finite NONEMPTY proper convex family; query in each domain; EVERY component ambient-continuous at query. FULL maximum subdifferential equals ordinary convex hull of ALL active subdifferentials, not just active union or closure.',
 'Example 2.27':'Hinge max(1-inner(z,x),0) full three-branch subdifferential{0},{-z},segment[-z,0]; no nonzero z restriction. Correct boundary branch includes every mixture.',
 'Theorem 2.28':'Affine precomposition f(Ax+b): adjoint(A)(partial f(Ax+b)) included in partial composite at x; proper f, no convexity/rank/qualification/composite-properness strengthening. Coordinate-free adjoint delta explicit.',
 'Definition 2.29':'L-Lipschitz on V subset effective domain: pairwise finite-value differences bounded by L distance; convention L nonnegative, no whole-domain premise.',
 'Theorem 2.30':'Proper convex f, nonnegative L: L-Lipschitz on ordinary domain interior iff every subgradient there has Euclidean norm<=L; empty interior and dimension0 allowed; signed-negative L boundary explicit.',
 'Lemma 2.31':'Every actual legal selected subgradient g supports loss difference by inner(g,x-u), for feasible x,u. No differentiability or arbitrary future-loss policy choice.',
 'Algorithm 2.2':'Output feasible decision before current loss, choose legal subgradient after feedback, project. Actual recursive selected-gradient policy with strict-prefix history; canonical choice exists and transported terminal bounds concern the same run.',
 'Example 2.32':'Absolute guessing on[0,1]: full translated absolute subdifferential and gradient-sign clamp recursion, actual legal arbitrary policy and canonical selection, sqrt(T) regret and upper-epsilon average rate; endpoint/middle selections retained.'}

def candidates(modules,names=None):
 out=[]
 for module in modules:
  assert module in by_module,module
  for d in by_module[module]:
   if names is None or d['name'] in names:out.append(d['full_name'])
 return sorted(set(out))

containers=[]
for old in nav['rows']:
 sid=old['source_id'];mods=module_map.get(sid,[])
 targets=candidates(mods,primary.get(sid)) if mods else []
 if old['required']:assert targets,sid
 containers.append(dict(source_id=sid,container_kind='numbered navigation or algorithm box',required=old['required'],
  source_pages=[pages[old['pdf_page']]],historical_inclusive_fragment=old['source_context_fragment'],historical_fragment_sha256=old['source_fragment_sha256'],
  exact_current_primary_declarations=targets,candidate_implementation_modules=mods,
  mathematical_intent=signatures.get(sid,old['reason_if_nonmathematical']),
  freeze_state='DRAFT: split exact semantic branches and review before chapter stabilization',
  inherited_historical_status_is_current_acceptance=False,chapter_accepted=False))

group_override={
 'extended-domain-indicator':['OnlineConvexExtended','OnlineConstraintFiniteLoss'],
 'interior-subgradient-existence':['OnlineSubgradientInterior'],
 'game-regret':['OnlineLearningRegret','OnlineNoRegretSemantics','OnlineLearningFTLState'],
 'actual-OSD-performance-transfer':['OnlineSubgradientDescent','OnlineSubgradientPolicy']}
for old in groups['source_groups']:
 mods=group_override.get(old['source_group'],[Path(p).stem for p in old['retrieved_existing_files']])
 intent=old['proposed_source_signature']
 if old['source_group']=='interior-subgradient-existence':
  intent='Proper convex extended-real f has actual ambient subgradient at EVERY ordinary interior point AND every relative-interior point, including lower-dimensional domains. Source footnote is mandatory. Current accepted migration includes actual relative-interior producer; historical flagged-only text is stale.'
 containers.append(dict(source_id='unnumbered:'+old['source_group'],container_kind='overlapping unnumbered source group',required=True,
  source_pages=[pages[p['pdf_page']] for p in old['pages']],mathematical_intent=intent,
  exact_current_primary_declarations=candidates(mods),candidate_implementation_modules=mods,
  declaration_list_scope='Candidate module context, not a claim that all listed helpers are separate source results or separate mandatory proof obligations.',
  freeze_state='DRAFT: exact formal branches, seven slots and overlap reconciliation pending',chapter_accepted=False))

extras=[
 ('strict-past-FTL-definition',[23,24],['OnlineFTLFailure','OnlineLearningFTLState'],'FTL selects an argmin of losses BEFORE the current round; any legal first action. No arbitrary whole-future-sequence algorithm existence.'),
 ('absolute-hinge-convex-nondifferentiable-introduction',[28],['OnlineSubgradientAbsolute','OnlineHinge'],'Absolute and hinge losses are convex and may be nondifferentiable at their kink. Nonzero hinge slope is needed for a genuine kink; slope0 is constant, not a counterexample.'),
 ('uncountably-many-nonsmooth-points',[31],['OnlineConvexNondifferentiability','OnlineConvexUncountability'],'In two dimensions coordinate |x1| is convex, nondifferentiable at every point of a line segment, whose points are uncountable. Do not replace by finite-dimensional scalar finite kink examples.'),
 ('relative-interior-footnote',[29],['OnlineSubgradientInterior'],'Footnote1 strengthens ordinary interior to relative interior. Actual ambient global support exists even on thin domains; ordinary interior emptiness does not discharge this claim.'),
 ('prescient-lookahead-nonpositive-stability',[26],[],'Main-text observation refers to15.5.1: learning current loss BEFORE prediction can make stability nonpositive. Separate prescient proximal identity from causal explicit OGD; constrained negative movement-square/Bregman term need not equal negative ordinary-gradient square. Exact chapter obligation/forward dependency classification awaiting independent source review.')]
for ident,pp,mods,intent in extras:
 containers.append(dict(source_id='additional:'+ident,container_kind='additional main-text claim audit',required=True,
  source_pages=[pages[p] for p in pp],mathematical_intent=intent,
  exact_current_primary_declarations=candidates(mods) if mods else [],candidate_implementation_modules=mods,
  freeze_state='DRAFT: must be reviewed, not excluded for difficulty',chapter_accepted=False,
  unresolved=not bool(mods)))
assert len(containers)==57
write(CONTRACT/'complete-source-reconciliation-draft-v1.json',dict(
 stage='draft, current shared declaration/provenance reconciliation after Chapter1 gate',chapter=2,source_sha256=PDF_SHA,
 source_fingerprint_sha256=sha(CONTRACT/'source-fingerprint-v1.json'),current_base=BASE,stacked_parent='PR203 OPEN draft, unmerged; not origin/main',
 navigation_containers=34,numbered_nonalgo_containers=32,algorithm_boxes=2,overlapping_unnumbered_groups=18,additional_claim_audits=5,
 source_audit_containers=57,independent_mandatory_obligation_total=None,proof_leaf_total=None,
 counting_boundary='Overlapping navigation/context/unnumbered containers are NOT57 independent theorems or an acceptance denominator. Numbered statements with multiple branches require exact child contracts before stabilization.',
 current_declaration_index=dict(path=(RUN/'current-online-declaration-retrieval-v1.json').relative_to(ROOT).as_posix(),sha256=sha(RUN/'current-online-declaration-retrieval-v1.json')),
 current_receipt_join=dict(path=(RUN/'prior-receipt-current-file-join-v1.json').relative_to(ROOT).as_posix(),sha256=sha(RUN/'prior-receipt-current-file-join-v1.json')),
 rows=containers,independent_history_and_problems='Section2.4 history and independent Problems2.1–2.5 separately optional; formal BODY claims whose proof is left as exercise remain required.',
 unresolved_required=['Exact seven-slot branch freeze and source-enumeration reviewer decision','Lookahead main-text claim versus forward dependency classification','Full current named public-value/canary/axiom, root/Tests/harness and relevant site integration gate after any actual changes','Chapter integration reader and shared registry source-qualified map','Scoped contribution, PR delivery and final review'],
 chapter_complete=False,book_complete=False,whole_Goal_status='ACTIVE'))
write(CONTRACT/'initial-dependency-dag-draft-v1.json',dict(
 stage='DRAFT source/proof route DAG; NOT certified proof-term implication graph',
 nodes=['extended-real-epigraph-domain','convex-closures','first-order-optimality','expectation-barycenter-minorant-Jensen','projection-existence-feasibility','gradient-source-adapter','causal-projected-OGD','variable-weighted-potential','fixed-variable-tuned-OGD','closed-proper','global-subgradient','ordinary-relative-interior-existence','differentiability-sum-max-affine-lipschitz-calculus','actual-OSD-policy','OSD-terminal-transfer','absolute-guessing-policy','Huber-guessing-comparison','units-policy-transport','causal-linearization','lookahead-source-classification','chapter2-source-contract-integration'],
 edges=[['extended-real-epigraph-domain','convex-closures'],['convex-closures','first-order-optimality'],['first-order-optimality','gradient-source-adapter'],['gradient-source-adapter','causal-projected-OGD'],['projection-existence-feasibility','causal-projected-OGD'],['causal-projected-OGD','variable-weighted-potential'],['variable-weighted-potential','fixed-variable-tuned-OGD'],['closed-proper','global-subgradient'],['global-subgradient','ordinary-relative-interior-existence'],['ordinary-relative-interior-existence','differentiability-sum-max-affine-lipschitz-calculus'],['global-subgradient','actual-OSD-policy'],['projection-existence-feasibility','actual-OSD-policy'],['actual-OSD-policy','OSD-terminal-transfer'],['OSD-terminal-transfer','absolute-guessing-policy'],['actual-OSD-policy','units-policy-transport'],['actual-OSD-policy','causal-linearization'],['fixed-variable-tuned-OGD','Huber-guessing-comparison'],['lookahead-source-classification','chapter2-source-contract-integration']],
 dependency_ready_first_leaf='Exact unchanged prior variable OGD terminal/current kernel readiness audit: inspected successful; no duplicate production proof or new mathematical progress.',
 source_classification_leaf='Independent reviewer classifies mandatory prescient main-text observation before any new target freeze; future Chapter15 pointer retained in whole-book dependencies if appropriate.',
 whole_Goal_status='ACTIVE'))
fixed()
print(json.dumps(dict(draft_containers=len(containers),actual_current_declarations=len(declaration_rows),prior_receipts=len(receipt_rows),manifests=len(manifest_rows),variable_build_inspected=True,chapter_complete=False)))
