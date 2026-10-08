from common_canary_v1 import *

canary_fixed()
targets = proving_fixed()['targets']
names = [t['name'] for t in targets]
boundary = ('Five derived behavioral-kernel realization endpoints; no five printed theorem attribution. '
    'One given Markov-kernel family on generated action and strict observation histories; no reduction of every arbitrary protocol, filtration or private-state algorithm to this model. '
    'The entire observation stream is exogenous and independent of the uniform tape: arbitrary temporal dependence is allowed for realization, action-dependent adaptive environments are not covered. '
    'Conditional kernel equality is AE under the actual history marginal; every-history sampler representation is a separate conclusion. '
    'The IID expected-fixed benchmark takes the infimum of expected fixed unit losses outside expectation; no hindsight min/expectation swap, rate, convergence, pathwise or high-probability bound. '
    'Classical family selection is an existence result, not a numerical sampler. '
    'Original16 Chapter1 source objects and null unknown proof total remain; all other Chapter1/2, unenumerated Chapters3-16 and necessary appendix obligations remain required. Whole Goal ACTIVE. '
    'Five bodies and13 public canary proofs compiled locally; combined root/Tests/fullharness/current site/FINAL/native/delivery gates pending. '
    'Stacked on OPEN draft unmerged PR199 exact'+BASE+'. Canonical main6847 and live site unchanged; no merge/deployment.')
source = ('Orabona arXiv:1912.13213v10,2026-06-21 SHA '+PDF_SHA+
    ': printed1/PDF13 IID squared-loss benchmark and Eqs1.1/1.2; printed3/PDF15 strict-past information. '
    'Given behavioral kernels and five realization declarations are derived formalization infrastructure. Printed round1 is Lean time0.')
proofs = [
    'Apply pinned Mathlib kernel randomization at every natural time and choose one jointly measurable sampler family before any observation law or horizon. Every history has the exact uniform pushforward law.',
    'Induct on the actual finite action recursion. Each step restricts both prefixes, generates prior actions and appends the current sample. Prove finite-input measurability, equality of every earlier action with the same infinite process, and pointwise nonanticipation.',
    'Independent infinite uniform coordinates give independence of the current draw from the strict past tape. The product law separates the entire observation stream from the tape. Regroup these blocks and map through the actual generated history, then through the sampler; the joint law is history marginal composed with the given kernel.',
    'Use the actual measurable generated prediction and established joint law. Conditional-distribution uniqueness identifies the kernel AE under the actual generated-history marginal, including time0.',
    'Select one sampler family first and retain its recursion, joint and conditional laws for every observation law. Under coordinate IID, same-law and AE unit observations, lift those assumptions through the product law. The concrete feasible history policy instantiates the existing IID expected-fixed excess producer at every natural horizon, including zero.'
]
maths = [r'\forall (\kappa_t)_t\ \exists(f_t)_t\ \forall t,h:\ (f_t(h,\cdot))_\#\mathrm{Unif}[0,1]=\kappa_t(h).',
    r'\begin{aligned}P_t&=f_t((P_{<t},Y_{<t}),U_t),\\U_{\le t}=U^{\prime}_{\le t},\ Y_{<t}=Y^{\prime}_{<t}&\Longrightarrow P_t=P^{\prime}_t.\end{aligned}',
    r'\mathcal L(H_t,P_t)=\mathcal L(H_t)\otimes\kappa_t,\quad H_t=(P_{<t},Y_{<t}).',
    r'\mathcal L(P_t\mid H_t)=\kappa_t(H_t)\quad\mathcal L(H_t)\text{-a.e.}',
    r'\begin{aligned}R_T&=\mathbb E\sum_{t<T}(P_t-Y_t)^2-\inf_{u\in[0,1]}\mathbb E\sum_{t<T}(u-Y_t)^2,\\&=\sum_{t<T}\mathbb E(P_t-\mathbb E[Y_0])^2\ge0.\end{aligned}'
]
titles = ['One sampler family before every law and horizon','The same causal recursion at every round',
    'Actual joint law from fresh uniform draws','Actual conditional law on reached histories',
    'One realized process and every-horizon IID excess']
local_parents = [[],[],['BanditRL.OnlineLearning.independent_private_seed_pair'],[names[1],names[2]],
    names[:4]+['BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess']]
external = ['Mathlib Kernel.exists_measurable_map_eq_unitInterval; no fabricated ABRL parent.',
    'Finite-coordinate measurability and Fin.snoc recursion; actual private helper verified in the compiled body.',
    'Mathlib iIndepFun_infinitePi, iIndepFun.indepFun_finset, indepFun_prod and product-map/compProd identities.',
    'Mathlib condDistrib_ae_eq_of_measure_eq_compProd, after the actual joint law.',
    'Existing shared randomized_history_policy_expectedFixed_excess supplies the fixed-expected benchmark calculation.']
notes = [dict(full_name=n,title=titles[i],chapter='online-foundations',featured=False,teaching_order=130+i,
    plain=proofs[i],math=maths[i],intuition='A fresh draw acts on an actually generated strict past.',
    why='Connect a specified randomized decision law to its causal process and exact probabilistic endpoint.',
    position=source,proof_idea=proofs[i],lean_notes=boundary+' '+external[i],dependencies=local_parents[i])
    for i,n in enumerate(names)]
plain = ' '.join(proofs)
card = dict(label='Causal realization of behavioral decision kernels',pages='printed1,3 / PDF13,15',pdf_page=13,
    url='https://arxiv.org/pdf/1912.13213v10',
    math=r'\begin{aligned}H_t&=(P_{<t},Y_{<t}),\\P_t&=f_t(H_t,U_t),\\\mathcal L(H_t,P_t)&=\mathcal L(H_t)\otimes\kappa_t,\\R_T^{\mathrm{expected\ fixed}}&=\sum_{t<T}\mathbb E(P_t-\mathbb E[Y_0])^2\ge0.\end{aligned}',
    plain=plain,fallback=plain,relationship=source,
    contract=dict(model='Given behavioral Markov kernels; one independent infinite uniform tape and actual generated unit actions.',
      assumptions='Joint kernel measurability and total mass1. Real observation law arbitrary for realization. IID coordinate independence, same law and AE unit observations for the expected-fixed clause. '+boundary,
      parameters='ONE sampler before ALL laws/horizons. Empty start, tape<=t and observations<t; naturalT0 allowed.',
      regret='Infimum of expected fixed unit losses outside expectation; population mean used only in analysis.',
      guarantee=plain+' '+boundary),local_status=dict(status='compiled',label='Compiled locally',boundary=boundary))
write(RUN/'reader-proposal-v1.json',dict(card=card,notes=notes,boundary=boundary,
    proposed_counts=dict(source_cards=1,public_proof_notes=5),not_yet_integrated=True))
write(RUN/'body-future-integration-scope-v1.json',dict(
    phase='After favorable BODY only: shared root/Test/reader/manifest integration',
    immutable=[PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix(),
      'lean-toolchain','lakefile.lean','lake-manifest.json'],
    exact_root_additions={'BanditRLProof.lean':'\nimport BanditRLProof.OnlineGuessingKernelCausal\n',
      'Tests.lean':'\nimport Tests.OnlineGuessingKernelCausalCanary\n'},
    reader_files=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'],
    reader_proposal=raw_index([RUN/'reader-proposal-v1.json']),
    reader_delta='Append exactly the bound source card and five proof notes on online-foundations; append its boundary to open_gaps/completion_blockers and exactly the public module to module_globs. Preserve every existing entry, label, status, URL and Book identity.',
    own_schema2_manifest='New own contribution manifest for exact5 frozen derived targets with truthful semantic/gate statuses; no old manifests or active SGB frontier changes',
    native_scope='Only own task/session suffixes and versioned evidence; own shadow and source16/null ledger; no global lifecycle memory/frontier replacement',
    retrieval_scope='Six indexes: generated timestamps and exactly these five actual public declarations only, preserving all existing records and order; baseline snapshots and independent delta review required',
    no_generated_site_edit=True,no_old_proof_or_statement_change=True,
    only_derived_obligations=5,original_source_objects=16,unknown_required_proof_total=None,
    arbitrary_protocol_reduction_required=True,chapter_complete=False,goal_complete=False))
print('Concrete reader and exact future integration proposal saved; no root/reader mutations.',flush=True)
