from common_canary_v1 import *
s=canary_contract_fixed()
audit=load(RUN/'compiled-audit-v1.json')
assert audit['whole_public_type_value_witnesses']==4 and audit['actual_canary_proofs']==11
names=[t['name'] for t in s['targets']]
boundary=('Four derived reconciliation results for the actual initial-half strict-past squared-loss FTL, not four printed source results. '
    'D1 is an exact iff for one all-time unit stream: literal comparator-wise finite nonpositive ordinary limits are equivalent to one feasible empirical-mean limit. Necessity adds no mean-convergence premise. '
    'D2 produces unit support from the explicit fixed binary dyadic recursion. D3 derives exact prefix counts and two diverging subsequences with distinct mean limits2/3 and1/3. '
    'D4 uses the SAME stream and learner: upper-epsilon NoRegret and true interval-best regret/T tends0 coexist with NO finite ordinary limit at fixed comparator0 and failure of literal LimitNoRegret. '
    'Signed regret can be negative; no contradiction to the source logarithmic upper bound. No future/horizon-selected observation or mean oracle, stochastic/minimax/all-algorithm impossibility claim. '
    'Pinned source ordinary-lim display, existing upper NoRegret and separately proposed source correction remain separate. Four bodies and eleven nondegenerate public canaries compiled locally; separate evidence in runs/online-ftl-obstruction-20261009. '
    'Only these four derived obligations may close after all gates. Original sixteen Chapter1 source objects/null unknown proof total, full Chapter1 reconciliation, other C1/C2, unenumerated C3-16 and necessary appendices remain REQUIRED. '
    'Whole Goal ACTIVE. Stacked on OPEN draft unmerged PR201 exact'+BASE+'. Main/live unchanged; no merge/deployment.')
source=('Orabona arXiv:1912.13213v10,2026-06-21 SHA '+PDF_SHA+
    ', printed2/PDF14 ordinary-limit no-regret display; printed4/PDF16 Theorem1.3 initial-half causal FTL and logarithmic upper bound; printed6/PDF18 sublinear guarantee. '
    'The four endpoints are derived reconciliation results. Source roundt+1 is Lean index t.')
proofs=[
    'Use the actual ordinary limits at feasible comparators0 and1. The signed-regret criterion yields convergence of the two squared distances. Their difference reconstructs convergence of the same empirical mean; actual feasible prefixes give a feasible limit. The reverse direction uses the prior conditional FTL producer.',
    'The explicit recursion is d0=0 and d(n+1)=1-d(floor(n/2)). Strong induction on the strictly smaller parent produces binary values and hence unit support at every index.',
    'Pair the two children of every binary-tree parent to derive S(2n+1)=2n-2S(n). Induction yields S(4^n-1)=2(4^n-1)/3 and the corresponding low-prefix count. Thus the high means are exactly2/3 and low means equal 1/3 - 1/(3*(2*4^n-1)). Both actual natural horizons diverge; inverse horizons tend0.',
    'Apply the existing actual-FTL upper guarantee and best-average-zero result to the support produced by D2. If fixed-zero regret/T had an ordinary finite limit, the squared empirical means would share one limit. Composing with both diverging D3 subsequences forces that limit to be both4/9 and1/9, a contradiction. The failure at feasible comparator0 rules out the literal all-comparator predicate.'
]
maths=[r'\bigl(\forall u\in[0,1],\ \exists a\le0:\ R_T(u)/T\to a\bigr)\ \Longleftrightarrow\ \exists m\in[0,1]:\bar y_T\to m.',
    r'd_0=0,\qquad d_{n+1}=1-d_{\lfloor n/2\rfloor},\qquad d_t\in[0,1].',
    r'\bar d_{4^{n+1}-1}\to\frac23,\qquad\bar d_{2\cdot4^n-1}\to\frac13.',
    r'\mathrm{UpperNoRegret}(p,d),\quad R_T^{\mathrm{best}}/T\to0,\quad\nexists a\in\mathbb R:R_T(0)/T\to a,\quad\neg\mathrm{LimitNoRegret}(p,d).']
titles=['Literal FTL no-regret iff the empirical mean converges','One explicit feasible dyadic observation stream',
    'Two distinct empirical-mean subsequence limits','Bounded actual FTL separates upper and ordinary no-regret']
parents=[['BanditRL.OnlineLearning.meanPredict_fixedRegret_limit_iff','BanditRL.OnlineLearning.meanPredict_limitNoRegret_of_mean_converges','BanditRL.OnlineLearning.empiricalMean_mem'],
    ['BanditRL.OnlineLearning.dyadicObservation'],['BanditRL.OnlineLearning.dyadicObservation'],
    [names[1],names[2],'BanditRL.OnlineLearning.meanPredict_noRegret','BanditRL.OnlineLearning.meanPredict_bestRegret_average_tendsto_zero','BanditRL.OnlineLearning.meanPredict_fixedRegret_limit_iff']]
notes=[dict(full_name=name,title=titles[i],chapter='online-foundations',featured=False,teaching_order=150+i,
    plain=proofs[i],math=maths[i],intuition='Sublinear upper regret does not by itself produce an ordinary fixed-comparator limit.',
    why='Reconcile the literal source definition with its actual bounded FTL guarantee.',position=source,
    proof_idea=proofs[i],lean_notes=boundary,dependencies=parents[i]) for i,name in enumerate(names)]
card=dict(label='A bounded actual-FTL obstruction and exact converse',pages='printed2,4,6 / PDF14,16,18',pdf_page=14,
    url='https://arxiv.org/pdf/1912.13213v10',math=maths[3],plain=' '.join(proofs),fallback=' '.join(proofs),relationship=source,
    contract=dict(model='One actual initial-half strict-past squared-loss FTL and one fixed deterministic unit observation stream.',
        assumptions='D1 all-time unit observations; D2-D4 derive the properties of an explicit stream with no external bound/limit oracle. '+boundary,
        parameters='Natural prefixes t<T; T0 empty sums and total division. Subsequence horizons4^(n+1)-1 and2*4^n-1 are positive and diverge.',
        regret='Signed fixed-comparator regret versus true feasible interval-minimum regret; deterministic pathwise statements.',
        guarantee=' '.join(proofs)+' '+boundary),local_status=dict(status='compiled',label='Compiled locally',boundary=boundary))
write(RUN/'reader-proposal-v1.json',dict(card=card,notes=notes,boundary=boundary,not_yet_integrated=True,
    proposed_counts=dict(source_cards=1,public_proof_notes=4)))
write(RUN/'body-future-integration-scope-v1.json',dict(phase='Only after favorable separate BODY review',
    immutable=[PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix(),'lean-toolchain','lakefile.lean','lake-manifest.json'],
    exact_root_additions={'BanditRLProof.lean':'\nimport BanditRLProof.OnlineFTLOscillation\n','Tests.lean':'\nimport Tests.OnlineFTLOscillationCanary\n'},
    reader_files=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'],
    reader_proposal=rows([RUN/'reader-proposal-v1.json']),
    reader_delta='Append exactly one bound sourcecard/four notes, one module_globs entry and boundary strings open_gaps/completion_blockers online-foundations; preserve ALL old records/status/URLs.',
    baseline_guard_conversion='Original baseline-v2 and CONTRACT189 remain immutable historical artifacts. New reviewed common_body_v2.py permits ONLY exact baseline root bytes plus approved import additions; all other rows unchanged. Reader changes validated exactly against new RAW integration baseline. No silent skip or historical unchanged claim after approved delta.',
    contribution_manifest='New own schema2 manifest for exactly four derived endpoints and one supporting definition; honest source/body/compiled/route/main/live states.',
    retrieval_scope='Own retrieval record/index only; all frozen global retrieval indexes immutable.',
    native_scope='Own append-only tasks/session suffixes and own trials/frontier/memory only; global SGB active_frontier/lifecycle_memory unchanged.',
    registry='Retain10964 complete existing shared registry records plus exactly5 new PUBLIC production nodes: dyadicObservation definition and four theorems. No per-Book proof tree.',
    no_generated_site_edit=True,no_old_proof_or_header_edit=True,only_derived_obligations=4,original_source_objects=16,
    unknown_required_proof_total=None,chapter_complete=False,goal_complete=False,final_site_gate_required=True,no_merge_deploy=True))
write(RUN/'candidate-body-status-v1.md','Four frozen actual production proofs and eleven exact public canaries focused compiled. Separate whole VALUE witnesses/axioms/direct graph/fences recorded. D4 v1 implicit-zero inference failure retained; v2 adds explicit zero types without changing header or previous bodies. Candidate only:0 accepted of4; BODY/rootTests/fullharness/currentsite/nonempty committed-HEAD contributor/FINAL/native/delivery pending. Only bounded same-FTL obstruction and all-comparator iff may close; original16/null/full Chapter1/other C1C2/C3-16/appendices remain. Goal ACTIVE.')
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(
    run_id=RUN.name,actual_body_targets=4,actual_canary_proofs=11,accepted_obligations=0,pending=4,
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),statement_hashes_unchanged=True,chapter_complete=False,goal_complete=False)))
