from common_canary_v1 import *
canary_contract_fixed()
audit=load(RUN/'compiled-audit-v1.json')
assert audit['whole_public_type_value_witnesses']==5 and audit['actual_canary_proofs']==12
names=[t['name'] for t in proving_fixed()['targets']]
boundary=('Five derived actual FTL limit hinges, not five printed results. F1/F2 allow arbitrary real observations for algebra; unit-game feasibility is not claimed for those unbounded streams. '
    'F3/F4/F5 require one all-time unit observation stream and the same initial-half strict-past meanPredict. F4 is a limit equivalence, not unconditional existence. '
    'F5 explicitly requires empiricalMean convergence; its limit m is analysis-only, never an algorithm input. Fixed-comparator limits may be strictly negative. '
    'The existing abstract unbounded-affine counterexample does not settle bounded actual FTL; a concrete bounded oscillating-mean obstruction and all-comparator converse remain separately required source reconciliation. '
    'Five bodies and twelve nondegenerate binary canaries compiled locally; semantic and complete acceptance evidence lives in runs/online-ftl-limit-20261009 and is recorded separately. '
    'Original sixteen Chapter1 source objects/null unknown proof total, other C1/C2, unenumerated C3-16 and necessary appendices remain required. Whole Goal ACTIVE; no chapter closure. '
    'Stacked on OPEN draft unmerged PR200 exact'+BASE+'. Main/live unchanged; no merge/deployment. No probabilistic/rate/high-probability or arbitrary-algorithm nonnegative-regret claim.')
source=('Orabona arXiv:1912.13213v10,2026-06-21 SHA '+PDF_SHA+
    ', printed2/PDF14 signed regret and ordinary-limit display; printed4/PDF16 Theorem1.3 actual FTL4log upper; printed6/PDF18 sublinear best-regret conclusion. '
    'The five Lean endpoints below are derived semantic hinges; the printed text and the existing upper-epsilon NoRegret remain separate. Source roundt+1 is Leant.')
proofs=[
    'Let Phi_T be the squared loss of the horizon empirical mean. The actual old leader minimizes the prefix of lengthT. Therefore Phi_(T+1) is at most Phi_T plus the actual next loss. Induct from the empty prefix to obtain Phi_T <= the actual FTL cumulative loss, without a supplied regret premise.',
    'Use the proved empirical-mean decomposition for positiveT, and empty sums forT0. Subtract that comparator loss from the same actual cumulative FTL loss. The minus T times squared-distance term is retained exactly.',
    'Identify the feasible interval minimum with the produced empirical mean. The actual FTL gap is nonnegative by the first endpoint and at most4+4logT by the source theorem. Divide by positiveT and squeeze between zero and a bound tending to zero.',
    'For positiveT, divide the exact comparator identity byT: normalized fixed regret equals normalized best regret minus squared distance from the empirical mean. The best term tends to zero. Subtract limits in both directions to obtain the ordinary-limit equivalence.',
    'Assume the empirical mean converges to m explicitly. Continuity gives squared-distance convergence to (u-m)^2 for every fixed realu. The exact equivalence gives fixed regret limit -(u-m)^2. This is nonpositive, so restricting comparators to[0,1] supplies the literal ordinary-limit predicate.'
]
maths=[r'\Phi_T=\sum_{t<T}(\bar y_T-y_t)^2\le\sum_{t<T}(p_t-y_t)^2,\quad R_T(\bar y_T)\ge0.',
    r'R_T(u)=R_T(\bar y_T)-T(u-\bar y_T)^2\quad(T\ge0).',
    r'0\le R_T^{\mathrm{best}}\le4+4\log T\quad(T\ge1),\qquad R_T^{\mathrm{best}}/T\longrightarrow0.',
    r'\frac{R_T(u)}{T}\longrightarrow a\quad\Longleftrightarrow\quad(u-\bar y_T)^2\longrightarrow-a.',
    r'\bar y_T\longrightarrow m\quad\Longrightarrow\quad\forall u\in\mathbb R:\ \frac{R_T(u)}{T}\longrightarrow-(u-m)^2\le0.'
]
titles=['A lower bound for the actual FTL loss gap','Exact signed fixed-comparator decomposition',
    'The actual best-comparator average tends to zero','The fixed-comparator ordinary-limit criterion',
    'Literal no-regret under empirical-mean convergence']
parents=[['BanditRL.OnlineLearning.empiricalMean_minimizes'],['BanditRL.OnlineLearning.empiricalMean_decomposition'],
    [names[0],'BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret','BanditRL.OnlineLearning.meanPredict_bestRegret_bound'],
    [names[1],names[2],'BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret'],[names[3]]]
external=['Finite-prefix induction and real ordered-ring arithmetic; existing meanPredict has exact strict-past semantics.',
    'Finite sums and ring arithmetic; no new minimizer premise.',
    'Mathlib squeeze_zero\u2032, Real.tendsto_pow_log_div_mul_add_atTop and natural-cast limit.',
    'Mathlib Filter.Tendsto.sub and congr\u2032; cancellation used only eventuallyT>0.',
    'Mathlib continuity of subtraction/square; LimitNoRegret retains the finite real limit witness.']
notes=[dict(full_name=name,title=titles[i],chapter='online-foundations',featured=False,teaching_order=140+i,
    plain=proofs[i],math=maths[i],intuition='The horizon mean separates signed fixed regret from the actual best-comparator gap.',
    why='Identify precisely which ordinary-limit conclusion follows for the same causal FTL strategy.',
    position=source,proof_idea=proofs[i],lean_notes=boundary+' '+external[i],dependencies=parents[i]) for i,name in enumerate(names)]
card=dict(label='Actual FTL regret and ordinary-limit semantics',pages='printed2,4,6 / PDF14,16,18',pdf_page=14,
    url='https://arxiv.org/pdf/1912.13213v10',
    math=r'\begin{aligned}R_T(u)&=R_T^{\mathrm{best}}-T(u-\bar y_T)^2,\\R_T^{\mathrm{best}}/T&\longrightarrow0,\\R_T(u)/T\longrightarrow a&\Longleftrightarrow(u-\bar y_T)^2\longrightarrow-a.\end{aligned}',
    plain=' '.join(proofs),fallback=' '.join(proofs),relationship=source,
    contract=dict(model='One actual initial-half strict-past squared-loss FTL predictor and signed comparator metrics.',
        assumptions='F1/F2 real streams unrestricted; F3/F4/F5 all-time unit observations. F5 additionally assumes empiricalMean convergence. '+boundary,
        parameters='NaturalT0 empty sums and total division; cancellation only at positiveT. Fixedrealu/a, eventual ordinary limits along natural horizons.',
        regret='Pathwise interval-minimum best regret versus fixed-comparator regret; no expectation or minE interchange.',
        guarantee=' '.join(proofs)+' '+boundary),local_status=dict(status='compiled',label='Compiled locally',boundary=boundary))
write(RUN/'reader-proposal-v1.json',dict(card=card,notes=notes,boundary=boundary,not_yet_integrated=True,
    proposed_counts=dict(source_cards=1,public_proof_notes=5)))
integration=dict(phase='Only after favorable separate BODY review',
    immutable=[PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix(),'lean-toolchain','lakefile.lean','lake-manifest.json'],
    exact_root_additions={'BanditRLProof.lean':'\nimport BanditRLProof.OnlineFTLLimitSemantics\n',
        'Tests.lean':'\nimport Tests.OnlineFTLLimitSemanticsCanary\n'},
    reader_files=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'],
    reader_proposal=rows([RUN/'reader-proposal-v1.json']),
    reader_delta='Append exactly bound one sourcecard/five notes online-foundations, boundary strings open_gaps/completion_blockers and one productionmodule_globs entry. Preserve ALL old records/status/URLs.',
    contribution_manifest='New own exact schema2 manifest, five derived declarations, honest separate semantic/compiled/route/main/live status.',
    retrieval_scope='Own task retrieval record/index only; six global indexes immutable unless a separately reviewed exact delta is needed.',
    native_scope='Own append-only task/stage/session suffixes and own trials/frontier/memory. GlobalSGB active_frontier and lifecycle_memory unchanged.',
    registry='Retain10959 complete existing shared registry records plus exactly5 new production theorem nodes; no perBook proof tree.',
    no_generated_site_edit=True,no_old_proof_or_header_edit=True,only_derived_obligations=5,
    original_source_objects=16,unknown_required_proof_total=None,chapter_complete=False,goal_complete=False,
    final_site_gate_required=True,no_merge_deploy=True)
write(RUN/'body-future-integration-scope-v1.json',integration)
write(RUN/'candidate-body-status-v1.md','All5 frozen actualFTL bodies and12 reviewed-header public binary canaries focused-compiled. Five whole public type/value witnesses,29 standard-only axioms, selected directVALUE graph and17fences safechecks passed. '
    'F1 prose-fence and unavailable pypdfium2 failures retained; configuration/runtime fallback repairs only. No terminal/source assumption weakened. '
    'Candidate only:0 accepted of5 until separate BODY review/root/Tests/fullharness/site/FINAL/native/delivery. Literal fixed-limit criterion retains negative-square and F5 convergence premise; bounded oscillating obstruction/all-comparator converse remain REQUIRED. WholeGoalACTIVE.')
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',
    json.dumps(dict(run_id=RUN.name,actual_body_targets=5,actual_canary_proofs=12,accepted_obligations=0,pending=5,
        public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),statement_hashes_unchanged=True,chapter_complete=False,goal_complete=False)))
print('Concrete reader and exact scoped integration proposal, no publication mutation.',flush=True)
