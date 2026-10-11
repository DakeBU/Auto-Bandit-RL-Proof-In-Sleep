from common import *
files = [PDF, ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean', PUBLIC,
    ROOT/'BanditRLProof/OnlineAdaptiveEnergy.lean', ROOT/'BanditRLProof/OnlineSubgradientDescent.lean',
    ROOT/'BanditRLProof/OnlineSubgradientPolicy.lean']
files += [CONTRACT/n for n in [
    'algorithm-definition-context-draft-v2.lean.txt', 'algorithm-regret_bound-header-draft-v1.lean.txt',
    'algorithm-neutral-packet-v1.lean.txt', 'algorithm-source-card-draft-v1.md',
    'algorithm-assumption-delta-draft-v1.md', 'parent-stabilized-v1.json', 'parent-proving-window-request-v1.md']]
files += [RUN/n for n in [
    'actual-step-BODY-parent-window-review-v1.md', 'actual-step-BODY-parent-window-review-v1.json',
    'actual-step-group-D-body-attempt-v2.lean.txt', 'actual-step-values-native-v1.json',
    'algorithm-blind-decoder-v1.md', 'algorithm-blind-decoder-v1.json',
    'worker-parent-route-v1.md', 'prove-parent-v1.py', 'verify-parent-v1.py',
    'parent-body-attempt-v1.lean.txt', 'parent-body-attempt-v2.lean.txt',
    'parent-focused-build-v1.json', 'parent-focused-build-v2.json', 'parent-compiled-local-v1.json',
    'parent-tactic-sequence-cleanup-v2.json', 'ParentPublicProbeV1.lean', 'parent-public-probe-v1.json',
    'parent-regret_bound-fence-native-v1.json', 'parent-regret_bound-safe-verify-v1.json',
    'parent-named-declarations-v1.json', 'ExportParentValueV1.lean', 'parent-value-export-v1.json',
    'parent-value-native-v1.json', 'parent-direct-parent-checks-v1.json', 'parent-compiled-trial-v1.json']]
assert all(p.is_file() for p in files)
write(RUN/'parent-BODY-review-inputs-v1.json', dict(files=rows(files),
    scope='Actual frozen single cumulative parent BODY review only; no source wrapper/benchmark/algorithm-canary or package acceptance.'))
write(RUN/'parent-BODY-review-packet-v1.md', '''# Review actual same-run cumulative parent BODY

Independently hash every indexed RAW before and after. Read FULL actual current source and unchanged header/context, original FULL parent neutral reconstruction and source deltas; prior favorable seven step BODY/parent-window decision authorizes exactly this one append. Check exact preservation of previous production prefix from retained Dv2 and exactly unchanged parent header. Parent v1 focused actual0 with unnecessary-sequence warning; v2 ONLY replaces final <;> ring with sequential ring, actual0, not failed proof. Read full source snapshots/log outputs, generic public application, axioms/fence/safe-verify/named declaration and compiled VALUE export (seven specified actual direct parents, not graph/necessity).

Review all boundary cases T0/D0/zero and leading-zero energy. For Dpositive,Tpositive actual same-run one_step is summed; weighted potential uses actual output membership/diameter and inclusive energy monotonicity, retains negative terminal norm-square with unrestricted aT; actual energy_eq_sum rewrites the existing energy bound. Only alpha,D are canceled in final algebra, never sqrt(total energy). No supplied future bound, exogenous energy or future-selected schedule. Check actual-prefix legality, EReal proper/support finite values, source-support-sufficient generalization and fixed-common-policy structural-causality limit. Parent is a derived strengthening; Eq4.4/Theorem4.14 source-convex and canonical variants, separately approved mathematical min/infimum repair with no Lean theorem yet, and actual algorithm canaries remain required.

Create-only parent-BODY-review-v1.md/.json UTF8singleLF in RUN with separate complete BODY verdict and exact RAW/index/report/header/current source hashes, all raw checks, truthful actor/history/source-view disclosures, required repairs if any, and remaining full gates. Do not edit production, prove additional statements, run tactics/builds, native accept or promote registry. Reuse prior source pixels honestly if no fresh viewing; hash pinned PDF. Review requested at GPT-6 Astra/medium as before; no runtime attestation or external/human/absolute-blind claim. Chapter partial/null, whole Goal ACTIVE.
''')
print(sha(RUN/'parent-BODY-review-inputs-v1.json'), len(rows(files)), flush=True)
