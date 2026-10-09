from common_v1 import *
import copy
fixed()
old=load(CONTRACT/'complete-source-reconciliation-draft-v1.json')
review=load(RUN/'source-enumeration-review-v1.json')
assert review['verdict']=='rejected' and not review['new_mathematics_accepted']
assert sha(RUN/'source-enumeration-review-v1.md')==review['report_sha256']
index=load(RUN/'current-online-declaration-retrieval-v1.json')
by_name={r['full_name']:r for r in index['rows']}
source=load(CONTRACT/'source-fingerprint-v1.json');pages={p['pdf_page']:p for p in source['source_pages']}
numbered={r['source_id']:r for r in review['numbered_source_branch_reviews']}
group_primary={
 'game-regret':['BanditRL.OnlineLearning.comparatorRegret','BanditRL.OnlineLearning.comparatorRegret_eq_sum','BanditRL.OnlineLearning.NoRegret','BanditRL.OnlineLearning.LimitNoRegret','BanditRL.OnlineLearning.limitNoRegret_implies_noRegret'],
 'extended-domain-indicator':['effectiveDomain','extendedIndicator','effectiveDomain_indicator','finite_add_indicator_iff','effectiveDomain_add_indicator'],
 'epigraph-domain-indicator-closure':['convex_effectiveDomain','convex_indicator_iff','convex_add_indicator'],
 'nonnegative-combination':['upperAdd','convex_nonneg_linear_combination'],
 'affine-composition':['convex_comp_affine'],
 'monotone-convex-composition':['convex_comp_monotone'],
 'pointwise-supremum':['convex_iSup'],
 'interior-first-order-optimality':['interior_min_iff_gradient_zero'],
 'fixed-unbounded-domain-residual':['BanditRL.OnlineGradientDescentSource.theorem_2_13_fixed'],
 'step-size-algebraic-minimization':['source_argmin','distance_energy_argmin','zero_distance_decreases','zero_energy_decreases','zero_coefficients'],
 'diameter-gradient-coarse-tuning':['diameter_argmin','BanditRL.OnlineGradientDescentSource.equation_2_1'],
 'closed-iff-lower-semicontinuous':['sourceClosed_iff_lowerSemicontinuous'],
 'subdifferential-domain':['subgradient_point_finite'],
 'interior-subgradient-existence':['subgradient_exists_of_domain_interior','subgradient_exists_of_relative_domain_interior'],
 'actual-OSD-performance-transfer':['BanditRL.OnlineSubgradientPolicy.regret_fixed','BanditRL.OnlineSubgradientPolicy.regret_variable_bound','BanditRL.OnlineSubgradientPolicy.regret_variable','BanditRL.OnlineSubgradientPolicy.regret_tuned','BanditRL.OnlineSubgradientPolicy.canonicalPolicy_legal','BanditRL.OnlineSubgradientPolicy.canonical_output','BanditRL.OnlineSubgradientPolicy.canonical_selected'],
 'unit-exponents':['unit_exponents','regret_unit_exponents'],
 'coordinate-rescaling':['gradient_scaled','step_scaling','wrong_step_scaling','output_scaling','legal_feedback_scaling','regret_scaling','wrong_step_output','upper_bound_scaling','regret_fixed_scaled'],
 'convex-to-linear-causal-reduction':['BanditRL.OnlineLinearization.output_linear_run','BanditRL.OnlineLinearization.output_prefix','BanditRL.OnlineLinearization.oracle_feedback','BanditRL.OnlineLinearization.trajectory_finite_loss','BanditRL.OnlineLinearization.regret_comparison','BanditRL.OnlineLinearization.regret_transfer','BanditRL.OnlineLinearization.canonical_regret_comparison']}
source_deltas={
 'Theorem 2.9':'Finite ordinary mean encoded by Bochner Integrable X, AE finite domain and measurability; no supplied loss-integrability. Existing negative-part/barycenter/minorant producers allow +infinite expectation. Source no-bottom f need not be proper a priori; AE finite domain yields witness.',
 'Theorem 2.8':'EReal implementation explicitly finite on open U and convex toReal on V; differentiability on U includes arbitrary open, not convex U. Source REAL-valued function is instantiated by coe, no silent global-convex U strengthening.',
 'Definition 2.20':'Shared support accepts arbitrary EReal, broader than printed proper convention; source consumers restore properness or construct it. No change to generic predicate.',
 'Theorem 2.21':'Repair ROOT draft-v1 intent: printed result is support existence on every point of convex V implies real f convex on V. It is NOT a Fermat/minimizer equivalence. Actual existing theorem_2_21 matches the printed convexity result.',
 'Theorem 2.22':'Finite-dimensional ambient real-germ differentiability, no false toReal/within-domain replacement; properness and domain interior derived, not silently imposed on terminal.',
 'Theorem 2.23':'Nonempty finite indexed family convention, one last-domain/other-ambient-interior witness. Aggregate may be all top even with proper components; generic support semantics are explicitly reviewed. No added aggregate-properness assumption.',
 'Theorem 2.26':'Finite nonempty family, every component ambient-continuous including inactive; ordinary hull of all active supports. No closure replacement or supplied full max-rule assumption.',
 'Theorem 2.28':'Coordinate-free real finite-dimensional adjoint represents printed transpose; no separately certified matrix-coordinate adapter or setting functor claimed. Inclusion only, no convex/rank/qualification strengthening.',
 'Definition 2.29':'Nonnegative L convention; real signed-negative constants can behave differently for singleton/zero-dimensional domains. Explicit convention, not proof of all-real source reading.',
 'Theorem 2.30':'L:NNReal permits0, zero dimension and empty ambient interior. Negative-L interpretation has an explicit historical counterexample/review; no silent scope equivalence.',
 'Example 2.15':'Delta>=0 including0, bounded actual features, real labels, known-horizon eta-run family; upper-epsilon comparison only. No ordinary signed-limit convergence or empirical financial guarantee.',
 'Example 2.14':'Actual tuned OGD squared-horizon lower/comparison producers support source suboptimality, not an inference from a loose O(sqrtT) upper bound.',
 'Lemma 2.31':'Repair ROOT draft-v1 intent: full TWO-INEQUALITY chain uses arbitrary current legal support, eta>0 and actual projection; not merely the support gap. Generic EReal finite-loss conversion uses properness and legal supports.',
 'Algorithm 2.2':'Source actual legal current support is implemented both by arbitrary played-legal finite-history oracle policy and one canonical choice. Prefix, feasibility, finite losses and same-run terminal transfer are separate producers.',
 'Theorem 2.13':'Finite T>0 for variable branch, source indexing translated to0..T-1/last eta(T-1), negative terminal retained. Fixed branch no diameter assumption; Hilbert extension explicitly broader than source Euclidean.'}

def exact_rows(names):
 result=[]
 for name in names:
  if name in by_name:r=by_name[name]
  else:
   found=[x for x in index['rows'] if x['name']==name]
   assert len(found)==1,(name,len(found));r=found[0]
  result.append(dict(declaration=r['full_name'],kind=r['kind'],module=r['file'],line=r['line'],native_header=r['native_header'],
   native_statement_hash=r['native_statement_hash'],complete_scope_and_BODY_sha256=r['source_file_sha256'],
   contribution_manifests=r['contribution_manifests'],prior_complete_file_matching_receipts=r['prior_receipts_with_matching_complete_file'],
   declaration_context_boundary=r.get('header_extraction_boundary',r['scope_context'])))
 return result

rows=[]
for item in old['rows']:
 row=copy.deepcopy(item);sid=row['source_id']
 if sid in numbered:
  row['mathematical_intent']=numbered[sid]['seven_slots']['conclusion']
 if sid.startswith('unnumbered:'):
  names=group_primary[sid.split(':',1)[1]]
  row['exact_current_primary_declarations']=[r['declaration'] for r in exact_rows(names)]
 if sid=='additional:strict-past-FTL-definition':
  row['exact_current_primary_declarations']=['BanditRL.OnlineFTLFailure.linearFTLPredict','BanditRL.OnlineFTLFailure.linearFTLPredict_minimizes','BanditRL.OnlineFTLFailure.linearFTLPredict_prefix','BanditRL.OnlineLearning.ftlPredict','BanditRL.OnlineLearning.ftlState_eq_predict']
 if sid=='additional:relative-interior-footnote':
  row['exact_current_primary_declarations']=['BanditRL.OnlineConvex.affine_support_of_relative_domain_interior','BanditRL.OnlineConvex.subgradient_exists_of_relative_domain_interior']
 if sid=='additional:uncountably-many-nonsmooth-points':
  row['exact_current_primary_declarations']=['BanditRL.OnlineConvex.coordinateAbsolute','BanditRL.OnlineConvex.convex_nondifferentiable_segment','BanditRL.OnlineConvex.coordinate_segment_not_countable','BanditRL.OnlineConvex.convex_uncountable_nondifferentiability']
 if sid=='additional:absolute-hinge-convex-nondifferentiable-introduction':
  row['exact_current_primary_declarations']=[]
  row['proposed_new_target_contract']=dict(path=(CONTRACT/'nonsmooth-targets-draft-v1.json').relative_to(ROOT).as_posix(),sha256=sha(CONTRACT/'nonsmooth-targets-draft-v1.json'))
  row['unresolved']=True
  row['mathematical_intent']='Printed shifted absolute |x-10| and labelled hinge max(1-y inner(z,x),0) convex but potentially nondifferentiable. New finite three-terminal draft gives exact pointwise iff and global zero-normal exception; separate source-repair verdict required.'
 row['exact_current_terminal_bindings']=exact_rows(row['exact_current_primary_declarations'])
 row['source_vs_Lean_delta']=source_deltas.get(sid,'See exact complete scoped terminal types, matching prior source/BODY/FINAL receipts and source-specific semantics; broader helper context is not a separate source obligation.')
 row['branch_contracts']=[dict(branch_id=sid+'::'+str(i+1),exact_terminal=t,
  boundary='Source branches can share one terminal or one branch can require several public producer dependencies; this list is a concrete declaration binding, NOT a count of independent source results.') for i,t in enumerate(row['exact_current_terminal_bindings'])]
 row['semantic_signature']=dict(
  objects='Pinned source Euclidean real objects/functions/sets; actual current complete module scoped context and native terminal types below. Scalar, extended-real, topology/probability distinctions remain explicit in mathematical_intent/source_vs_Lean_delta.',
  quantifiers='Exact universal/existential quantifier order is the attached native terminal with its complete module section context; source-specific all-point/all-comparator/current-policy/finite-family order stated in mathematical_intent.',
  assumptions='All source assumptions in mathematical_intent and all actual Lean assumptions in exact_current_terminal_bindings. No new regularity is introduced by this reconciliation; differences in source_vs_Lean_delta and prior scoped reviews retained.',
  conclusion=row['mathematical_intent'],
  constants_and_normalization='Exact source anchors and actual native formulas attached; source1..T mapsLean0..T-1; sharp terminal residuals, unit constants, closed support segments and nonnegative Lipschitz convention are not discarded.',
  probability_and_information='Static convex-analysis rows are deterministic. Jensen uses an actual probability measure/integrable random vector and extended expectation. Algorithm rows output before current feedback, with actual prefix/feasibility/selected-feedback producers. No whole-future algorithm existence substitutes for causality.',
  boundary=row['source_vs_Lean_delta']+' Chapter integration, all new proofs and shared reader gates remain unaccepted; whole Goal ACTIVE.')
 row['freeze_state']='proposed stabilized SOURCE INVENTORY version2; exact reused-terminal identities fixed, new nonsmooth terminal review pending, chapter proof/acceptance not certified'
 rows.append(row)

forward=[
 ('chapter5-unbounded-variable-OGD-failure',[26],5,'Section5.2: time-varying OGD can fail on unbounded domains; retain as future lower-bound/algorithm-failure dependency, not inferred from the failure of a proof bound.'),
 ('chapter5-oracle-distance-energy-rate-impossibility',[27],5,'Oracle eta using comparator distance and future eta-dependent gradients is not a causal choice; full claimed impossibility refers to Chapter5 lower bound.'),
 ('chapter5-DLsqrtT-minimax-optimality',[27],5,'Optimal up to constants requires a separate minimax lower bound, not supplied by Equation2.1 upper bound.'),
 ('chapter3-unbounded-SGD',[26],3,'Stochastic setting permits certain varying-rate SGD on unbounded domains; statistical assumptions/model and rate supplied by Chapter3, not adversarial OGD claim.'),
 ('chapter4-adaptive-oracle-like-rates',[27],4,'Section4.2 adaptive rates can resemble unavailable oracle rates under their exact modified guarantees.'),
 ('chapter4-square-OGD-improvement',[27],4,'Later Chapter4 tunes/analyzes OGD to obtain improved squared-guessing performance; current generic eta~1/sqrtT package remains suboptimal.'),
 ('chapter7-FTL-analysis',[20],7,'Chapter7 source forward analysis route; do not infer arbitrary FTL guarantee from Example2.10 failure or the special squared mean predictor.'),
 ('chapter13-parameter-free-oracle-like-rates',[27],13,'Parameter-free algorithms give specified oracle-like rates with additional terms/regimes; current algebraic minimization is not this algorithm.')]
for ident,pp,target,intent in forward:
 # Some forward navigation text lies in another inclusive fragment. The full page
 # and independently reviewed intent are retained; source reviewer must confirm anchors.
 rows.append(dict(source_id='forward:'+ident,container_kind='required whole-book forward source dependency',required=True,
  source_pages=[pages[p] for p in pp],target_chapter=target,mathematical_intent=intent,
  exact_current_primary_declarations=[],exact_current_terminal_bindings=[],
  dependency_status='required/open future chapter; no completed current theorem asserted',
  chapter_gate_policy='Forward model/theorem is preserved in whole-book required ledger. A later chapter source/statement enumeration must close or explicitly repair it. Chapter2 local guarantees are separately audited; no claim that the forward theorem is already proved.',
  source_claim_complete=False,chapter_accepted=False))
new=copy.deepcopy(old);new.update(stage='source-inventory repair draft version2 for distinct review',rows=rows,source_audit_containers=len(rows),
 exact_native_binding_count=sum(len(r.get('exact_current_terminal_bindings',[])) for r in rows),
 forward_dependencies_open=1+len(forward),
 supersedes=dict(path=(CONTRACT/'complete-source-reconciliation-draft-v1.json').relative_to(ROOT).as_posix(),sha256=sha(CONTRACT/'complete-source-reconciliation-draft-v1.json'),retained=True),
 source_review_v1=dict(path=(RUN/'source-enumeration-review-v1.json').relative_to(ROOT).as_posix(),sha256=sha(RUN/'source-enumeration-review-v1.json'),verdict='rejected for draft stabilization; exact enumeration repairs, no rejection of current mathematics'),
 mandatory_proof_total=None,source_acceptance=False,
 explicit_repairs=['E1-E4 additional mandatory branches joined or exact new nonsmooth draft','E5 negative Bregman movement distinct forward model','E6 whole-book forward references required/open','E7 exact current native-header/full-scope/provenance bindings attached, overlapping counts not proof counts','E8 source conventions/deltas explicit','ROOT v1 Theorem2.21 and Lemma2.31 intention errors corrected without changing any old theorem'])
write(CONTRACT/'complete-source-reconciliation-draft-v2.json',new)

# Preserve actual CLI bootstrap templates before replacing only OWN files.
for folder in ['tasks','proof-obligations','conversion-windows']:
 p=ROOT/folder/(TASK+'.md');write(RUN/(folder+'-bootstrap-template-v1.md'),p.read_bytes())
task='''# Chapter2 source integration and finite nonsmooth examples

Task id: `ONLINE-CH2-CHAPTER-AUDIT-20261009`
Kind: `lean`
Status: `draft / source enumeration repair`
Harness: `hierarchical`

Whole Chapters1–16 Goal ACTIVE. Chapter1 local gate and final exact-head delivery accepted on097359ac; stacked PR203 OPEN draft/unmerged, canonical origin/main6847b678 unchanged. Chapter2 is not accepted.

Pinned source: Orabona arXiv1912.13213v10 June21; PDF SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Physical20–35/printed8–23 all original images personally reread. Source/card/version2 exact bindings in docs/contracts/online-ch2-chapter-audit-v1. Old source/navigation and rejected draft/review preserved.

Source inventory version2 has65 overlapping audit containers (34 numbered/algorithm navigation,18 unnumbered groups,5 additional claims,8 forward dependencies). This is NOT65 independent theorem/proof obligations; totals remain null. Numbered branch contracts attach exact actual public headers/full scoped BODY hashes and actual prior receipt joins. Required forward references stay open in the whole-book ledger.

First finite new mathematical leaf: three frozen-proposal terminals for two example families, shifted absolute and labelled hinge, in NEW BanditRLProof/OnlineNonsmoothExamples.lean. No production code before exact contract/repair review. Reuse actual full support, singleton-gradient and convex/calculus APIs. Blind/source roles distinct per AGENTS and semantic-roundtrip; no human/external review claim.

First dependency-ready existing leaf: variable OGD exact prior contracts and full current source-file FINAL match, actual focused9107jobs and whole-type kernel pass, seven standard axiom records. This is current readiness/reuse evidence, not new proof progress or chapter acceptance.

Allowed: OWN source/contract/run/task ledgers; later new finite module/canary and append-only public imports after reviewed freeze. Shared old proofs, tools/pins, active globalSGB/frontier/trials/memory, old reader content and generated _site preserved. Read-only/scoped retrieval uses actual CLI with OWN outputs. Repeated proof failure => typed repair without terminal weakening.

Acceptance remaining: source inventory/finite terminal stabilization; actual producer and public canaries/axioms; precise reused-source review and current roots/Tests/full harness; shared registry/source reader and site; contributor gate, scoped commit/push/reviewable PR and distinct final review. No merge/deploy authorized by local compilation.
'''
(ROOT/'tasks'/(TASK+'.md')).write_bytes(task.encode('utf8'))
obligations='''# Proof obligations: Chapter2

Task id: `ONLINE-CH2-CHAPTER-AUDIT-20261009`

| Node | Exact boundary | Dependencies / route | State |
| --- | --- | --- | --- |
| SOURCE-V2 | All main-text numbered/unnumbered branches and required forward dependencies; exact native/scoped provenance join | Source v10 images, rejected E1–E8 review retained, complete-source-reconciliation-draft-v2.json | repair / independent review pending |
| REUSE-VARIABLE | Two unchanged sharp variable OGD public terminals, real same-run recurrence | projection/first-order/weighted potential/source adapter; exact earlier distinct reviews/full-file RAW match | current focused and kernel evidence inspected; no new math |
| NEW-ABS | Global convexity and exact DifferentiableAt iff x≠c | actual mathlib convex affine translation, abs derivative/off0 and nonderivative0 | exact proposal frozen for review, proving not started |
| NEW-HINGE | Convexity and ambient differentiability iff inner(a,x)≠1 | actual full support set, differentiability singleton, local affine branches | exact proposal frozen for review, proving not started |
| NEW-LABEL | Source labelled hinge, all real y/features and global differentiability iff y•z=0 | NEW-HINGE; construct real margin boundary for nonzero normal | exact proposal frozen for review; source qualification separately reviewed |
| FORWARD | Prescient movement/Chapter5 lower bounds/Chapter3 SGD/Chapter4 improvements/Chapter7 FTL/Chapter13 parameter-free | required future chapter source contracts, no naive gradient sign flip | open REQUIRED whole-book dependencies |
| GATE | Public canaries/axioms, source/statement hashes, root/Tests/full harness, shared registry/site and reviewer | all local source obligations closed with explicit forward-reference boundary | pending |
| DELIVERY | Scoped contributor contract, commit/push/reviewable PR and exact final review | GATE, stacked base explicit | pending |

Failure records: bootstrap defaultPython38 lacks pypdfium2 (actual1); source resumed with official bundled runtime(actual0). Source enumeration v1 rejected for precision; v2 repair does not alter existing mathematical statements. ROOT v1 Theorem2.21/Lemma2.31 prose intention errors explicitly corrected. No new proof attempts yet, no blocked Goal status.

Independent Problems2.1–2.5 optional; formal main-text results whose proof is left as exercise required. Mandatory proof-leaf total unknown/null. Whole Goal ACTIVE.
'''
(ROOT/'proof-obligations'/(TASK+'.md')).write_bytes(obligations.encode('utf8'))
conversion='''# Conversion window: Chapter2

Task id: `ONLINE-CH2-CHAPTER-AUDIT-20261009`

Version2 source inventory: docs/contracts/online-ch2-chapter-audit-v1/complete-source-reconciliation-draft-v2.json. Full current declaration retrieval and actual reviewed-file join in OWN RUN. Initial DAG is a source/proof route overlay, not certified proof-term implication.

| Source object | Lean mapping | Critical boundary |
| --- | --- | --- |
| x_t,g_t,eta_t and Pi_V | existing shared Domain/project/iterateVariable/gradient; actual source adapter | source rounds1..T -> Lean0..T-1; current feedback after output; negative terminal retained |
| shifted absolute | fun x:real => abs(x-c), printedc=10 | actual ambient derivative iff x≠c; no domain-only derivative |
| labelled hinge | fun x:E => max(1-y*inner(z,x),0) | same1/0, arbitrary real label/feature; effective normaly•z; smooth iff margin≠1; globally smooth iff normal0 |
| generic support / proper source | SourceSubdifferential and source consumers | no silent replacement of proper by generic ALL-EReal behavior |
| lower-semicontinuous/relative-interior/uncountable | actual current named producers | source footnotes and same-function cardinality included, no scalar-finite-kink replacement |
| lookahead | required forward prescient proximal/Bregman movement model | observing current loss first is different information; constrained negative movement is not ordinary gradient-square |

Exact proposed new headers, native hashes, seven slots, allowed paths and separate source qualification in nonsmooth-targets-draft-v1.json; neutral decoder packet in OWN RUN. Retrieval commands actually run with OWN indexes, no global registry/frontier mutation. Lower proof work awaits distinct contract/repair review. No toolchain/dependency upgrade or mathematical weakening permitted.

Chapter2 local source acceptance and whole-book required forward proofs remain distinct; no chapter/Goal completion or main/live update asserted.
'''
(ROOT/'conversion-windows'/(TASK+'.md')).write_bytes(conversion.encode('utf8'))

book=load(ROOT/'docs/contracts/online-book-v1/coverage.json')
assert len(book['chapters'])==16 and book['chapters'][0]['accepted']
ledger=copy.deepcopy(book)
ledger['chapters'][1]=dict(chapter=2,status='draft-source-enumeration-repair-v2',accepted=False,mandatory_count=None,
 source_audit_container_count=len(rows),independent_proof_leaf_total=None,source_inventory=(CONTRACT/'complete-source-reconciliation-draft-v2.json').relative_to(ROOT).as_posix(),
 first_new_leaf='Two introductory nonsmooth example families, three exact public terminal proposals; independent statement/repair review pending',
 prior_variable_current_readiness=(RUN/'variable-readiness-inspected-v1.json').relative_to(ROOT).as_posix(),
 boundary='Full chapter gates not passed; historical pending migration strings not current proof-gap claims. All whole-book forward dependencies remain required/open. Canonical Book coverage not updated before reviewed stabilization.')
ledger['snapshot_scope']='OWN Chapter2 proposal of existing shared Book ledger; no canonical ledger mutation, no per-Book Lean library. Every other chapter row preserved exactly.'
write(CONTRACT/'whole-book-coverage-proposal-v1.json',ledger)

native('chapter-draft-event-v1','lifecycle-event','--session',TASK,'--event','draft','--payload-json',json.dumps(dict(
 run_id=RUN.name,source_fingerprint=sha(CONTRACT/'source-fingerprint-v1.json'),source_inventory_v2=sha(CONTRACT/'complete-source-reconciliation-draft-v2.json'),
 source_containers=len(rows),proof_leaf_total=None,source_review_pending=True,new_math=0,chapter_complete=False,goal_complete=False,
 workflow_enforcement='Native event record; semantic roles/review and edit permissions separately documented, not a single enforced runtime.'),separators=(',',':')))
native('chapter-repair-event-v1','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(
 rejected_scope='source enumeration draft stabilization only',review_receipt=sha(RUN/'source-enumeration-review-v1.json'),repairs='E1-E8 and two root prose-intention corrections; version1 retained, old proofs unchanged',
 repaired_inventory=sha(CONTRACT/'complete-source-reconciliation-draft-v2.json'),chapter_complete=False,goal_complete=False),separators=(',',':')))
fixed();print('Version2 exact source/native binding repair and OWN actual draft/repair events written; whole-book Goal ACTIVE.')
