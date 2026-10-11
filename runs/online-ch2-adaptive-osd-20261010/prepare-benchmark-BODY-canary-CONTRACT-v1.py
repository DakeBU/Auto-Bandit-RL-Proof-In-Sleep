from common import *
decoder = RUN/'algorithm-canary-blind-decoder-v1.json'
assert decoder.is_file()
capture('algorithm-canary-api-retrieval-v2', 'rg', '-n',
    'theorem (affine_convex|affine_proper|affine_subdifferential|project_unitInterval|energy_eq_sum|output_succ|state_prefix|regret_bound|source_eq4_4|source_theorem4_14_infimum)',
    ROOT/'BanditRLProof/OnlineHinge.lean', ROOT/'BanditRLProof/OnlineGuessingOGD.lean',
    ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean', ROOT/'BanditRLProof/OnlineAdaptiveBenchmark.lean')
files = [PDF, ROOT/'BanditRLProof/OnlineAdaptiveBenchmark.lean', ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean',
    ROOT/'BanditRLProof/OnlineOptimalStep.lean', ROOT/'BanditRLProof/OnlineHinge.lean',
    ROOT/'BanditRLProof/OnlineGuessingOGD.lean', ROOT/'BanditRLProof/OnlineSubgradientDescent.lean',
    ROOT/'BanditRLProof/OnlineSubgradientPolicy.lean', ROOT/'BanditRLProof/OnlineConvexExtended.lean',
    ROOT/'runs/online-ch2-adaptive-summation-20261010/source-pdf52-v1.png',
    ROOT/'runs/online-ch2-reconciliation-20261010/forward-readonly-retrieval/source-pdf52-text-v1.txt']
files += list(CONTRACT.glob('benchmark-*'))+list(CONTRACT.glob('algorithm-canary-*'))
files += [CONTRACT/'minimum-infimum-repair-proposed-v1.md',
    CONTRACT/'algorithm-definition-context-draft-v2.lean.txt']
files += list(RUN.glob('benchmark-*.json'))+list(RUN.glob('benchmark-*.lean.txt'))
files += list(RUN.glob('algorithm-canary-*.json'))+list(RUN.glob('algorithm-canary-*.md'))
files += [RUN/n for n in ['prove-benchmark-v1.py','repair-resume-benchmark-v2.py',
    'verify-benchmark-v1.py','verify-benchmark-v2.py','BenchmarkPublicProbeV1.lean','BenchmarkPublicProbeV2.lean',
    'BenchmarkTypeProbeV1.lean','ExportBenchmarkValuesV1.lean','draft-algorithm-canary-v1.py',
    'AlgorithmCanaryTypeProbeV1.lean','AlgorithmCanaryTypeProbeV2.lean',
    'specialization-BODY-benchmark-CONTRACT-review-v1.md','specialization-BODY-benchmark-CONTRACT-review-v1.json',
    'potential-canary-BODY-minimum-review-v1.md','potential-canary-BODY-minimum-review-v1.json',
    'algorithm-canary-blind-decoder-v1.md','algorithm-canary-blind-decoder-v1.json',
    'director-algorithm-canary-draft-v1.md','architect-algorithm-canary-draft-v1.md']]
assert all(p.is_file() for p in files)
write(RUN/'benchmark-BODY-canary-CONTRACT-inputs-v1.json',dict(files=rows(files),
    scope='Separate actual five benchmark BODYs and seven proposed actual-run canary CONTRACT decisions.'))
write(RUN/'benchmark-BODY-canary-CONTRACT-packet-v1.md', '''# Benchmark BODY and actual-run canary CONTRACT review

Hash every indexed RAW before/after. Read FULL five actual benchmark BODYs, exact favorable reviewed context/header/window, actual snapshots and sequential focused receipts. First GLB actual compiler1 had one local algebra residual b²+D²*0=b²; append ring only in that BODY, frozen unchanged, v2 actual0 before any downstream append. All downstream individual actual0. External public probe v1 omitted owning new-module import, actual1 retained; v2 import-only probe correction actual0, no production/statement change. Public probe applies all five FULL statements including four positive-minimum blocks and two source conjunctions. Five standard-only axioms/fences/safe-verify/named declarations and actual compiled direct VALUEs checked. Strict decrease alone is not GLB greatestness: inspect explicit b/S or D²/b objective b/2 test. Infimum nonempty image witness eta1 and lower-bound/glb; exact mixedzero/bothzero/positive attainment; no sqrtS cancellation at zero. Source performance and corrected scalar equality use same realized alpha=sqrt2/2 energy, not rerun/clairvoyant optimizer. Pinned source/previous min repair unchanged; withdrawn false /2 allegation stays withdrawn. Give separate benchmark_BODY verdict; no full package acceptance.

Then review seven exact canary headers, context v2 (NOT v1), neutral reconstruction and draft TYPE probes/API search/source/reuse card. Context v2 only adds existing OnlineHinge import before any production BODY, to reuse affine_convex/affine_proper/full affine_subdifferential. All seven headers and concrete fixture values unchanged from v1; neutral packet semantics unchanged. No new-source math/assumption change or toolchain upgrade. V=[0,1], initial1/2, fixed time-only supports0,3,0,-4, affine finite proper convex losses, alpha1/D1. Actual selected/energy and outputs/etas/active projection must follow the existing recurrence, no assumed trajectory. General-alpha energy equality is valid because fixed policy ignores history, not because arbitrary adaptive trajectories share energies. Full trace has13 facts. Performance has4 components: actual residual parent59/10, Eq4.4 15/2, source4.14 sqrt50 and repaired actual energy infimum equality. All branch VALUEs must reuse intended public parents, not numeric-only proofs. Prefix has equality of full state at2 and actual changed whole loss2 plus unchanged loss1. Zero-energy fixture has nonzero terminal distance1/4 but weighted residual0; D0 singleton has selected3/energy9, no false zero-gradient inference. Proper/global supports/convexity produced, not assumed; fixed policy legality only on chosen affine stream, no universal off-path OracleLaw. Bound branches on zero fixtures must call actual regret_bound. Source scope is derived synthetic checks of Chapter2 forward dependencies, not new printed theorems or Chapter4/book completion.

If benchmark BODY and canary CONTRACT both favorable, approve create-only Tests/OnlineAdaptiveOSDCanary.lean with EXACT algorithm-canary-context-draft-v2.lean.txt, seven unchanged header/BODYs and namespace closure only. Ordered individual leaves: loss_regular, feedback_energy, trace_canary, performance_canary, prefix_canary, zero_energy_canary, zero_diameter_canary. Each actual focused success before next append; stop actual failure with retained snapshot/log, BODY-only repair allowed. No extra helpers/defs/imports, no old production/root/Test-root/registry/readers/global/native acceptance. Approve exact context/header RAWs and normalized statement hashes plus allowed/forbidden edit window separately from future canary BODY acceptance.

Create-only benchmark-BODY-canary-CONTRACT-review-v1.md/.json UTF8singleLF in RUN. Include two distinct verdicts benchmark_BODY_verdict/canary_CONTRACT_verdict, full per-target seven-slot audit, exact all RAW checks/current source/index/report hashes, required_blocking_repairs and approved_conditional_edit_window with path/create_only/context_path/context_sha256/headers[target,path,sha256]/ordered_groups/individual_success_prerequisite/allowed/forbidden. Truthfully disclose staged actor/history/personal source pixels vs prior pixel reuse, no absolute-blind/human/external or runtime-model attestation. Do not prove/run tactics/builds/edit inputs/native accept. Full canary BODY/public/fences/axioms/VALUE/distinct BODY review and combined root Tests full harness/registry readers/shadow site pixels FINAL/native/post-native/delivery still required. Chapter2 partial/null/all8 forward open; whole Goal ACTIVE.
''')
print(sha(RUN/'benchmark-BODY-canary-CONTRACT-inputs-v1.json'),len(rows(files)),flush=True)
