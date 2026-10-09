from common import *
fixed()
types=load(RUN/'neutral-type-index-v1.json')
assert len(types['targets'])==7
assert sha(RUN/'neutral-types-v1.txt')==types['context_sha256']
assert sha(RUN/'neutral-blind-receipt-v1.json')=='e5f8721a309750a01ef7063e51ceda96653745b26c0293a410768f7ab1ba43e9'
source=load(RUN/'source-bindings.json')
for row in source['rows']:
    n=row['pdf_page'];assert sha(RUN/f'source-pdf{n}.txt')==row['text_sha256'] and sha(RUN/f'source-pdf{n}.png')==row['image_sha256']
    row.update(text_path=(RUN/f'source-pdf{n}.txt').as_posix(),image_path=(RUN/f'source-pdf{n}.png').as_posix())
source.update(pdf_path=PDF.as_posix(),source_url='https://arxiv.org/pdf/1912.13213v10',version_date='2026-06-21',
    anchors='Chapter2 printed14/PDF26 first post-Theorem2.13 bullet; Section15.5.1, Algorithm15.8/Theorem15.30 printed265-266/PDF277-278',
    source_intent='Knowing current loss before choosing current prediction permits a proximal update and negative Bregman movement energy. For quadratic Euclidean regularizer and affine loss, the proximal step is projection of prior state minus eta times current vector. The source general theorem and changing-eta branch are not claimed proved by this specialization.',
    root_personally_viewed_pages=[26,277,278],public_source_correction=False)
write(CONTRACT/'source-card-v1.json',source)
slots=dict(
    objects='Complete real inner-product E, Domain E is actual nonempty closed convex carrier with constructed metric projection. Finite Euclidean source specializes; complete Hilbert extension disclosed. Linear/affine losses inner(g_t,x)+b_t, fixed eta>0. Deterministic.',
    quantifiers='Every Domain, positive eta, arbitrary full vector/offset sequences, arbitrary initial center x0 in E, every natural T including0 and every comparator u in V. Definitions select unique projection each round; no arbitrary future-informed existential algorithm or supplied minimizer/stability inequality.',
    assumptions='No bounded domain, gradient bound, nonzero vector or T>=1. Source quadratic regularizer has X=E, so initial x0 may lie outside V; every played prediction is feasible. Nonempty/closed/convex/complete supplies projection existence. Eta=0 or negative excluded in inequality denominators; feasibility/prefix/algebra need no positivity.',
    conclusion='Actual projected iterate minimizes known-current affine loss plus squared movement/(2eta); actual one-step comparator inequality; same-run telescope retains BOTH negative final distance and cumulative movement energy; source-form corollary discards only nonpositive final distance. Seven terminals serve one producer chain, not7 printed source theorems.',
    normalization='Lean state0=x0, state(t+1)=source played x_(t+1); Lean roundt corresponds source roundt+1. prediction t=state(t+1). Regret sum t in rangeT. Movement state(t+1)-state(t); final stateT. All squares divided by2eta. Negative movement is not generally eta/2 times ordinary gradient norm square on constrained V.',
    information='Current g_t received BEFORE prediction t. Explicit recursion/prefix theorem restricts prediction t to g_0..g_t and excludes future g. This is prescient with respect to standard online loss order; no claim of ordinary strict-past OGD. Regret algebra covers arbitrary b_t that cancels. No probability/adaptive-measure assumption.',
    boundary='Reusable affine-loss Euclidean foundation growth for REQUIRED Chapter2 prescient forward reference. The full convex/subdifferentiable loss, general Bregman regularizer and variable-step Theorem15.30 remain required, as do all other Chapter2 forwards. This specialization does NOT close the full source container, Chapter2, Chapter15 or whole Goal. No general OMD/Tsallis/RL/merge/deployment/main/live claim.')
dag=dict(advance_sharp_bound=['actual project_spec','norm_eq_iInf_iff_real_inner_le_zero','norm_sub_sq_real'],
    advance_proximal_minimizer=['advance_sharp_bound','project_spec','norm square nonnegative'],prediction_mem=['project_spec','actual recursion'],
    prediction_prefix=['actual recursion','current-inclusive vector prefix'],regret_eq_loss_difference=['inner_sub_right','sum algebra'],
    regret_sharp_bound=['advance_sharp_bound','actual recursion','Finset.sum_range_succ'],regret_source_bound=['regret_sharp_bound','nonnegative terminal distance'])
write(CONTRACT/'targets-draft-v1.json',dict(stage='draft before distinct source/contract review',source_card_sha256=sha(CONTRACT/'source-card-v1.json'),
    complete_context_path=(RUN/'neutral-types-v1.txt').as_posix(),complete_context_sha256=sha(RUN/'neutral-types-v1.txt'),targets=types['targets'],seven_slots=slots,
    initial_dependency_DAG=dag,conversion_window='Finite7 frozen types for one same-run producer chain. Only first dependency-ready advance_sharp_bound may begin after favorable CONTRACT review and versioned stabilization. Rejected hypotheses/targets get a new version, never silent in-place weakening.',
    permitted_initial_proof_file=PUBLIC.as_posix(),future_canaries='Separate frozen contracts and distinct blind/source review before integration; active bounded projection, unbounded domain, current-vs-future dependency and T0 boundaries planned.',
    permitted_metadata=[RUN.as_posix(),CONTRACT.as_posix(),'tasks/'+TASK+'.md','proof-obligations/'+TASK+'.md','conversion-windows/'+TASK+'.md'],
    forbidden='Old baseline/current roots/readers/global SGB/index/private/frozen/generated_site/model escalation/other chapters; root/Test appends or reader changes need exact candidate publication plans and applicable gates.',
    mathematical_progress='First fixed terminal from true projection; then actual proximal producer and same-run regret endpoint. No source-container closure or chapter fraction from count7.',chapter_proof_total=None,chapter_complete=False,whole_Goal_status='ACTIVE'))
write(RUN/'20_architect-draft-v1.md','Use existing Domain/project/project_spec and pinned Hilbert variational characterization, not duplicate projection theory. For P001 derive eta<g,p-u> <= <x-p,p-u> from actual projection at x-eta g; three-point norm identity yields sharp movement inequality. P002 uses P001 plus norm nonnegative to prove actual selected proximal argmin/feasibility. Prefix proves inclusive current index from Nat recursion, never strict-past. Telescope scaled energy on exactly the same sequence, retaining terminal and movement; source-form only drops terminal. No theorem body before independent source/contract stabilization. The affine/Euclidean restriction is explicit reusable foundation; full prescient observation remains open. Planned canary V=[-1,1],x0=1,eta=1/2,g0=6,g1=-1,u=0 gives played(-1,-1/2), regret-11/2, terminal1/4,movement17/4, sharp RHS-7/2. False negative ordinary-gradient-energy RHS-17/2 is violated. This is hypothetical until actual public bodies compile. Unconstrained same vectors give equality-21/2; do not confuse projected/unconstrained identities.')
capture('retrieval-pinned-APIs-v1','lake','env','lean',RUN/'Retrieval.lean')
event('draft-native-v1','draft',dict(scope='7 precise affine/Euclidean prescient proposed terminals for one Chapter2 dependency foundation; full source observation remains open',
    contract_sha256=sha(CONTRACT/'targets-draft-v1.json'),source_sha256=sha(CONTRACT/'source-card-v1.json'),blind_receipt_sha256=sha(RUN/'neutral-blind-receipt-v1.json'),source_review_pending=True,chapter_complete=False,goal_complete=False))
fixed()
paths=[p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
paths += [ROOT/'BanditRLProof/OnlineGradientDescent.lean',ROOT/'lean-toolchain',ROOT/'lakefile.lean',ROOT/'lake-manifest.json',PDF]
write(RUN/'contract-review-inputs-v1.json',dict(rows=rows(paths),stage='draft source/contract anti-anchored review; no theorem body/compiled claim',whole_Goal_status='ACTIVE'))
print('Source/7type/semantic/DAG/conversion/retrieval/native draft packet ready; distinct source review required.')
