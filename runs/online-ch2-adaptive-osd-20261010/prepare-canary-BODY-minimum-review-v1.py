from common import *
files = [PUBLIC, ROOT/'Tests/OnlineAdaptivePotentialCanary.lean', PDF,
    ROOT/'BanditRLProof/OnlineOptimalStep.lean',
    ROOT/'runs/online-ch2-adaptive-summation-20261010/source-pdf52-v1.png']
files += [CONTRACT/n for n in [
    'potential-canary-context-draft-v1.lean.txt', 'potential-canary-header-1-draft-v1.lean.txt',
    'potential-canary-header-2-draft-v1.lean.txt', 'potential-canary-stabilized-v1.json',
    'potential-canary-contract-draft-v1.md', 'potential-canary-neutral-v1.lean.txt',
    'algorithm-source-card-draft-v1.md', 'minimum-infimum-repair-proposed-v1.md']]
files += [RUN/n for n in [
    'potential-BODY-and-canary-CONTRACT-review-v1.md', 'potential-BODY-and-canary-CONTRACT-review-v1.json',
    'potential-canary-blind-decoder-v1.md', 'potential-canary-blind-decoder-v1.json',
    'potential-canary-body-attempt-v1.lean.txt', 'potential-canary-body-attempt-v2.lean.txt',
    'potential-canary-body-input-v2.json', 'potential-canary-hash-wrapper-failure-v1.json',
    'potential-canary-proof-repair-v2.json', 'potential-canary-failed-trial-v1.json',
    'potential-canary-focused-build-v1.json', 'potential-canary-focused-build-v2.json',
    'prove-potential-canary-v1.py', 'resume-potential-canary-v2.py', 'repair-potential-canary-v2.py',
    'verify-potential-canary-v1.py', 'PotentialCanaryPublicProbeV1.lean', 'potential-canary-public-probe-v1.json',
    'ExportPotentialCanaryConjunctValuesV1.lean', 'potential-canary-value-export-v1.json',
    'potential-canary-values-native-v1.json', 'potential-canary-compiled-trial-v1.json',
    'potential-canary-fence-1-native-v1.json', 'potential-canary-fence-2-native-v1.json',
    'potential-canary-safe-verify-1-v1.json', 'potential-canary-safe-verify-2-v1.json',
    'algorithm-optimum-API-retrieval-v1.json']]
assert all(p.is_file() for p in files)
write(RUN/'potential-canary-BODY-minimum-inputs-v1.json', dict(files=rows(files),
    scope='Bounded canary BODY review and separate proposed minimum/infimum source repair, not algorithm or package acceptance.'))
write(RUN/'potential-canary-BODY-minimum-packet-v1.md', '''# Two separately decided reviews

Independently hash all fixed RAW before/after. First inspect the two entire potential canary BODYs against frozen context/headers, source-isolated decode, prior prospective authorization, actual failed compiler output and same-header tactic repair, actual successful focused/public generic checks/axioms/fences and compiled selected VALUE branches. Four selected inequality conjuncts must visibly retain the public production proof; check actual C4/C3/zero-weight/T1 arguments and arithmetic. Wrapper failure removing :=by is metadata only; no silent header mutation. State precise BODY verdict and scope; no full harness or parent OSD closure.

Separately inspect minimum-infimum-repair-proposed-v1, algorithm-source-card-draft-v1, pinned original PDF52 and existing shared OnlineOptimalStep actual statements. Search for counterexamples or missing assumptions. Decide the PROPOSED repair of Theorem4.14's displayed min equality for one-zero coefficients, including actual attainability in source-compatible examples; keep original source untouched, both-zero attained case, positive unique argmin, future-energy same-trajectory distinction. A favorable mathematical repair verdict is not a compiled IsGLB/benchmark theorem, not algorithm CONTRACT acceptance and not author endorsement. Do not decide the algorithm recurrence/terminal: its source-blind decode and next contract review are separate.

Write create-only potential-canary-BODY-minimum-review-v1.md/.json in this RUN, UTF8 single LF. Include two separate verdicts, blocking repairs, all fixed RAW checks, manifest/report SHA, explicit model/history/no runtime/human/external attestation limits. No other edits, no acceptance mutation, no Goal complete. No new library/Test/root/reader/registry edit window is requested here.
''')
print('Bounded two-verdict review packet created.', flush=True)
