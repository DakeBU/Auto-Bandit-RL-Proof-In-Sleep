from common import *
files = [ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean', PUBLIC,
    ROOT/'BanditRLProof/OnlineSubgradientPolicy.lean']
files += [CONTRACT/n for n in [
    'algorithm-definition-context-draft-v2.lean.txt', 'algorithm-state_succ-header-draft-v1.lean.txt',
    'algorithm-state_prefix-header-draft-v1.lean.txt', 'algorithm-regret_bound-header-draft-v1.lean.txt',
    'algorithm-fingerprints-draft-v1.json', 'algorithm-stabilized-v1.json',
    'algorithm-contract-draft-v1.md', 'algorithm-source-card-draft-v1.md',
    'algorithm-neutral-packet-v1.lean.txt', 'algorithm-prefix-neutral-v1.lean.txt']]
files += [RUN/n for n in [
    'algorithm-CONTRACT-review-v1.md', 'algorithm-CONTRACT-review-v1.json',
    'algorithm-blind-decoder-v1.md', 'algorithm-blind-decoder-v1.json',
    'algorithm-prefix-blind-decoder-v1.md', 'algorithm-prefix-blind-decoder-v1.json',
    'worker-causal-state-route-v1.md', 'prove-causal-state-v1.py',
    'state-succ-body-attempt-v1.lean.txt', 'state-prefix-body-attempt-v1.lean.txt',
    'state-succ-compiled-local-v1.json', 'state-succ-focused-build-v1.json', 'state-prefix-focused-build-v1.json',
    'CausalStatePublicProbeV1.lean', 'causal-state-public-probe-v1.json',
    'state_succ-fence-native-v1.json', 'state_prefix-fence-native-v1.json',
    'state_succ-safe-verify-v1.json', 'state_prefix-safe-verify-v1.json',
    'causal-state-named-declarations-v1.json', 'ExportCausalStateValuesV1.lean',
    'causal-state-value-export-v1.json', 'causal-state-values-native-v1.json',
    'causal-state-compiled-trial-v1.json', 'verify-causal-state-v1.py']]
assert all(p.is_file() for p in files)
write(RUN/'causal-state-BODY-inputs-v1.json', dict(files=rows(files),
    scope='Two actual structural BODYs/eight definitions only; no parent regret/benchmark/whole package acceptance.'))
write(RUN/'causal-state-BODY-packet-v1.md', '''# Anti-anchored actual causal state BODY review

All fixed RAW independently hashed before/after. Inspect actual8definitions and two theorem BODYs, frozen context/header identity, the first state_succ focused build before prefix was added, exact retained prefix bytes and second focused build, public full generic examples/axiom outputs/fences, direct compiled TYPE/VALUE rows for actual8definitions+2theorems and prefix's actual state_succ parent. Read mathematical dependence rather than accepting exit0 or counts. Both focused commands show Built and build-completed markers; imported old warnings are retained and no old source edit was made.

First proof rfl establishes actual Nat.rec joint state update, second inducts with full loss-function strict-prefix equality and fixed common parameters/policy, reconstructs equal finite past tuple and rewrites current consumed function. No exogenous eta equality or desired performance premise. Retain exact information restriction and source-support generalization. Parent negative-terminal regret_bound remains frozen outside production, not proved. T0/state initialization covered structurally, no regret zero-case claim yet. Check no hidden axiom/sorry or altered context; source decode history/API slice incident stays disclosed.

Write create-only causal-state-BODY-review-v1.md/.json UTF8singleLF with all RAW checks, report/manifest/production/context/header hashes, BODY verdict/remaining repairs, direct dependency evidence and honest boundaries. This review requests no new edit window or acceptance/native/global mutation. Next bootstrap10definitions-derived targets have only draft headers/TYPE and separate pending neutral decode; do NOT review/authorize them without their next fixed packet. Full root/Tests/harness/registry/site/algorithm canary/performance/benchmark/FINAL/native/delivery remain pending. Goal active.
''')
print('Actual causal BODY review packet prepared.', flush=True)
