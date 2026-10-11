from common import *
public = ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean'
assert public.read_bytes() == (RUN/'specialization-canonical_theorem4_14-body-attempt-v1.lean.txt').read_bytes()
assert load(RUN/'specialization-direct-parent-checks-v1.json')['all_expected_found']
d = load(RUN/'benchmark-blind-decoder-v1.json')
assert not d['unresolved_ambiguities'] and sha(d['report']) == d['report_sha256']
assert sha(d['input_path']) == d['input_sha256']
capture('benchmark-retrieval-v1', 'rg', '-n',
    'theorem (lower_bound|distance_energy_argmin|optimal_unique|zero_distance_decreases|zero_energy_decreases|zero_coefficients)|theorem IsGLB.csInf_eq',
    ROOT/'BanditRLProof/OnlineOptimalStep.lean',
    ROOT/'.lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean')
write(RUN/'director-benchmark-draft-v1.md', 'Finish the required printed scalar comparator equality honestly: all-nonnegative infimum, exact attainable regimes, full positive unique minimum, linked as a complete conjunction to the same actual source-convex trajectory guarantee. Do not omit mixed-zero regimes or optimize rerun learners.')
write(RUN/'architect-benchmark-draft-v1.md', 'Five exact headers in one proposed new module. Reuse frozen OnlineOptimalStep APIs and Mathlib IsGLB.csInf_eq. First IsGLB finite leaf, then scalar factor/attainment/positive unique minimum, finally complete source conjunction only after favorable actual source endpoint BODY review. Each predecessor actual focused success before downstream append. No new definitions/helpers/import upgrades or existing production edit.')
files = [PDF, public, PUBLIC, ROOT/'BanditRLProof/OnlineAdaptiveEnergy.lean',
    ROOT/'BanditRLProof/OnlineOptimalStep.lean', ROOT/'BanditRLProof/OnlineConvexExtended.lean',
    ROOT/'BanditRLProof/OnlineSubgradientDescent.lean', ROOT/'BanditRLProof/OnlineSubgradientPolicy.lean',
    ROOT/'.lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean',
    ROOT/'runs/online-ch2-adaptive-summation-20261010/source-pdf52-v1.png',
    ROOT/'runs/online-ch2-reconciliation-20261010/forward-readonly-retrieval/source-pdf52-text-v1.txt']
for file in ['specialization-stabilized-v1.json', 'benchmark-fingerprints-draft-v1.json']:
    key = 'exact_headers' if file.startswith('specialization') else 'headers'
    files += [Path(row['path']) for row in load(CONTRACT/file)[key].values()]
files += [CONTRACT/n for n in ['algorithm-definition-context-draft-v2.lean.txt',
    'specialization-stabilized-v1.json', 'specialization-source-card-draft-v1.md',
    'specialization-neutral-packet-v2.lean.txt', 'benchmark-context-draft-v1.lean.txt',
    'benchmark-fingerprints-draft-v1.json', 'benchmark-neutral-packet-v1.lean.txt',
    'benchmark-source-card-draft-v1.md', 'benchmark-conversion-window-draft-v1.md',
    'minimum-infimum-repair-proposed-v1.md']]
files += [RUN/n for n in ['parent-body-attempt-v2.lean.txt', 'parent-BODY-review-v1.md',
    'parent-BODY-review-v1.json', 'specialization-CONTRACT-review-v1.md',
    'specialization-CONTRACT-review-v1.json', 'specialization-blind-decoder-v1.md',
    'specialization-blind-decoder-v1.json', 'specialization-blind-decoder-v2.md',
    'specialization-blind-decoder-v2.json', 'worker-specializations-route-v1.md',
    'prove-specializations-v1.py', 'verify-specializations-v1.py',
    'SpecializationPublicProbeV1.lean', 'specialization-public-probe-v1.json',
    'ExportSpecializationValuesV1.lean', 'specialization-value-export-v1.json',
    'specialization-values-native-v1.json', 'specialization-direct-parent-checks-v1.json',
    'specialization-named-declarations-v1.json', 'specialization-compiled-trial-v1.json',
    'BenchmarkTypeProbeV1.lean', 'benchmark-type-probe-v1.json', 'benchmark-retrieval-v1.json',
    'draft-benchmark-v1.py', 'benchmark-blind-decoder-v1.md', 'benchmark-blind-decoder-v1.json',
    'director-benchmark-draft-v1.md', 'architect-benchmark-draft-v1.md',
    'potential-canary-BODY-minimum-review-v1.md', 'potential-canary-BODY-minimum-review-v1.json']]
for name in load(CONTRACT/'specialization-stabilized-v1.json')['exact_headers']:
    files += [RUN/('specialization-'+name+n) for n in ['-body-attempt-v1.lean.txt',
        '-focused-build-v1.json', '-compiled-local-v1.json', '-fence-native-v1.json', '-safe-verify-v1.json']]
assert all(p.is_file() for p in files)
write(RUN/'specialization-BODY-benchmark-CONTRACT-inputs-v1.json', dict(files=rows(files),
    scope='Separate actual four source endpoint BODY decisions and five benchmark CONTRACT/proving-window decisions.'))
write(RUN/'specialization-BODY-benchmark-CONTRACT-packet-v1.md', '''# Separate source endpoint BODY and exact benchmark CONTRACT review

Hash all fixed indexed RAW independently before/after. First inspect all four actual source/canonical BODYs against exact favorable CONTRACT, actual current production and each individual sequential focused snapshot/receipt; complete generic public examples with unchanged hconvex, standard axiom outputs, literal-assumption fences/safe-verify and selected direct compiled VALUE parents. Prior parent bytes/context/eight definitions remain unchanged up to namespace-end relocation. Explicit hconvex is unused by the sufficient-support parent in two source wrappers, deliberately retained, with actual linter warnings not suppressed; canonical wrappers pass it through. Source drop only nonnegative terminal, exact alpha1 and sqrt2/2 coefficients and same-run energy; both canonical adapters derive actual-prefix legality from canonical_feedback at identical alpha. All four BODY verdicts must be separate from benchmark future proof acceptance.

Then inspect original pinned PDF52, source min equality, the prior separately favorable mathematical min/infimum repair and exact new five headers/context/neutral full reconstruction/TYPE/API probe/retrieval/source card/DAG/conversion. The scalar image is {b | exists eta>0,b=upperBound(D²)S eta}, held-coefficient real set; IsGLB includes lower/greatestness, no attainment. sInf source factor must prove meaningful nonempty bounded image. Attainment iff (D>0 and S>0) or bothzero; positive minimum header retains candidate admissible/value/all-positive lower bound/equality iff. Final source conjunction retains BOTH complete actual source performance and repaired infimum equality with the same realized energy; not an oracle optimizing rerun trajectories. Source-convexity/global supports/proper EReal values/initial-comparator feasible/zero skip/T0/D0/zero energy remain. Never add D/Spositive to whole performance to rescue source printed min. This exact proposed correction is distinct from unchanged original and withdrawn /2 allegation; no author endorsement.

If source BODYs AND exact benchmark CONTRACTs favorable, permit only a new OnlineAdaptiveBenchmark.lean with EXACT frozen context and FIVE unchanged headers/BODYs; no existing production changes/new imports outside context/defs/helpers/root/Test/registry/readers/global edits. Approve dependency-ready ordered finite groups: benchmark_isGLB first; then source_benchmark_value, benchmark_attained_iff, benchmark_positive_minimum; finally source_theorem4_14_infimum after source BODY favorable and preceding actual focused success. Each individual appended leaf must actually focus-compile before downstream append; stop on failure, BODY-only repair, statement changes version/review. Proving approach as exact conversion card, no tactics by reviewer.

Create-only specialization-BODY-benchmark-CONTRACT-review-v1.md/.json UTF8singleLF in RUN. Return separate source_BODY and benchmark_CONTRACT verdicts, per-target seven-slot audit (all four BODYs and all five contracts), blocking repairs or exact new-file context/header hashes, ordered groups and allowed/forbidden window. All RAW/index/report/source/current production hashes, actual evidence scope, source-view/history/actor limitations and remaining gates recorded. No production change/proof/build/native accept. Requested Astra/medium not runtime attestation, reused distinct staged actor not external/human/absolute blind. Actual benchmark BODY/public/axiom/fences/VALUE/BODY-review, nondegenerate actual algorithm canary/full root Tests harness/registry reader/shadow site FINAL/native/delivery still required. Chapter2 partial/null/all8 forward open; whole Goal ACTIVE.
''')
print(sha(RUN/'specialization-BODY-benchmark-CONTRACT-inputs-v1.json'), len(rows(files)), flush=True)
