from common import *
public = ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean'
f = load(CONTRACT/'bootstrap-stabilized-v1.json')
files = [public, ROOT/'BanditRLProof/OnlineGradientDescent.lean',
    ROOT/'BanditRLProof/OnlineSubgradientDescent.lean', ROOT/'BanditRLProof/OnlineSubgradientPolicy.lean']
files += [Path(row['path']) for row in f['exact_headers'].values()]
files += [CONTRACT/n for n in [
    'algorithm-definition-context-draft-v2.lean.txt', 'algorithm-regret_bound-header-draft-v1.lean.txt',
    'algorithm-source-card-draft-v1.md', 'bootstrap-neutral-packet-v1.lean.txt',
    'bootstrap-contract-draft-v1.md', 'bootstrap-stabilized-v1.json', 'bootstrap-fingerprints-draft-v1.json']]
files += [RUN/n for n in [
    'bootstrap-CONTRACT-review-v1.md', 'bootstrap-CONTRACT-review-v1.json',
    'bootstrap-blind-decoder-v1.md', 'bootstrap-blind-decoder-v1.json',
    'worker-bootstrap-route-v1.md', 'prove-bootstrap-v1.py', 'verify-bootstrap-v1.py',
    'state-prefix-body-attempt-v1.lean.txt', 'BootstrapPublicProbeV1.lean', 'bootstrap-public-probe-v1.json',
    'bootstrap-named-declarations-v1.json', 'ExportBootstrapValuesV1.lean',
    'bootstrap-value-export-v1.json', 'bootstrap-values-native-v1.json',
    'bootstrap-direct-parent-checks-v1.json', 'bootstrap-compiled-trial-v1.json']]
for letter in 'ABCDE':
    files += [RUN/('bootstrap-group-'+letter+n) for n in [
        '-body-attempt-v1.lean.txt', '-focused-build-v1.json', '-compiled-local-v1.json']]
    d = load(RUN/('bootstrap-group-'+letter+'-focused-build-v1.json'))
    assert d['actual_exit'] == 0
    assert b'Build completed successfully' in base64.b64decode(d['stdout_base64'])
for name in f['exact_headers']:
    files += [RUN/('bootstrap-'+name+n) for n in [
        '-fence-native-v1.json', '-safe-verify-v1.json']]
assert all(p.is_file() for p in files)
assert load(RUN/'bootstrap-direct-parent-checks-v1.json')['all_expected_found']
write(RUN/'bootstrap-BODY-inputs-v1.json', dict(files=rows(files),
    scope='Ten actual same-run bootstrap BODYs only; no performance/benchmark/algorithm-canary/whole package acceptance.'))
write(RUN/'bootstrap-BODY-packet-v1.md', '''# Anti-anchored ten bootstrap BODY review

RAW hash all indexed inputs before/after. Inspect full actual algorithm with old two structural BODYs and new ten exact theorem BODYs; compare context/all exact header fingerprints. Verify all five source snapshots preserve prior successful prefix (except moved namespace end), and actual A→E focused build evidence shows compiler Built/build-completed before downstream source was written. Review mathematics of skip/projection feasibility and support/finite-loss/OracleLaw/canonical adapter, not just exit codes or declaration counts. Every header was approved before tactics, no imported assumptions changed and no new helpers/definitions/imports appear.

Inspect ten FULL public generic examples, #print axioms actual stdout, all frozen fences, named declaration lookup and actual compiled VALUE rows with explicit parent checks: true state recurrence, project_spec, energy sum, finite_loss, and canonicalPolicy_legal are actually consumed. Direct constants are neither a full graph nor proof-necessity evidence. No ten-source-result claim, no arbitrary-policy legality claim, no absolute causality for reselected external parameters/policy. Degenerate signs/zero cases of structural headers remain included. Main negative-terminal regret header remains frozen outside production; no regret closure or new minimum benchmark yet.

Write create-only bootstrap-BODY-review-v1.md/.json UTF8singleLF in this RUN, with all RAW/index/report/production/context/header hashes, exact BODY verdicts, retained limitations and any blocking repairs. This asks for no new edit window, native acceptance, global mutation or further proof tactics. Actual one-step/performance/benchmark/canary/full combined/publication/FINAL/native/delivery gates remain required; package/chapter/Goal remain open. Disclose reused distinct staged automated actor, no human/external/runtime/absolute-blind attestations.
''')
print('Ten actual bootstrap BODY review packet ready.', flush=True)
