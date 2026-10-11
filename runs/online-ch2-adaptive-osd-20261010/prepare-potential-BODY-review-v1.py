from common import *
decoder = load(RUN/'potential-canary-blind-decoder-v1.json')
assert decoder['inputs_unchanged'] and not decoder['ambiguities']
assert sha(decoder['input_path']) == decoder['input_sha256']
assert sha(decoder['report']['path']) == decoder['report_sha256']
assert sha(RUN/'potential-canary-blind-decoder-v1.json') == '8303d8b1932ee9a97a6eb96d92750f8b60aea67783da510c8acfd0571144e92e'
files = [PUBLIC, PDF,
    ROOT/'.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Module.lean']
files += [CONTRACT/n for n in [
    'source-card-v1.md', 'source-card-v2.md', 'source-proof-display-correction-proposed-v1.md',
    'source-proof-display-retraction-v1.md', 'potential-definition-context-v1.lean.txt',
    'potential-header-draft-v1.lean.txt', 'potential-contract-draft-v2.md',
    'potential-stabilized-v2.json', 'algorithm-terminal-draft-v1.md', 'DAG-draft-v1.json',
    'potential-canary-context-draft-v1.lean.txt',
    'potential-canary-header-1-draft-v1.lean.txt', 'potential-canary-header-2-draft-v1.lean.txt',
    'potential-canary-neutral-v1.lean.txt', 'potential-canary-contract-draft-v1.md']]
files += [RUN/n for n in [
    'baseline-v1.json', 'source-pdf25-v1.png', 'source-pdf26-v1.png',
    'potential-contract-review-v1.json', 'potential-CONTRACT-review-v1.md',
    'potential-contract-review-v2.json', 'potential-CONTRACT-review-v2.md',
    'worker-potential-route-v1.md', 'potential-body-attempt-v1.lean.txt', 'potential-body-input-v1.json',
    'neutral-potential-packet-v1.lean.txt', 'neutral-potential-reconstruction-v1.md',
    'neutral-potential-reconstruction-v1.json', 'potential-review-packet-path-failure-v1.json',
    'prove-potential-v1.py', 'potential-bootstrap-import-failure-v1.json',
    'potential-focused-build-v1.json', 'PotentialPublicProbeV1.lean', 'potential-public-probe-v1.json',
    'potential-fence-v1.json', 'potential-fence-native-v1.json', 'potential-safe-verify-v1.json',
    'potential-named-declaration-v1.json', 'potential-compiled-trial-v1.json',
    'potential-canary-blind-decoder-v1.md', 'potential-canary-blind-decoder-v1.json',
    'PotentialCanaryTypeProbeV1.lean', 'potential-canary-type-probe-v1.json',
    'ExportPotentialValuesV1.lean', 'potential-value-export-v1.json', 'potential-values-native-v1.json',
    'potential-local-evidence-v1.json', 'verify-potential-and-draft-canary-v1.py', 'potential-extra-probes-v1.py']]
assert all(p.is_file() for p in files)
write(RUN/'potential-BODY-and-canary-CONTRACT-inputs-v1.json', dict(
    boundary='Bounded proof/validation review input set, not a whole-repository RAW baseline or final package acceptance.',
    files=rows(files)))
write(RUN/'potential-BODY-and-canary-CONTRACT-packet-v1.md', '''# Anti-anchored BODY and complete canary-CONTRACT review

Read the fixed input manifest; independently hash every listed RAW before/after. Inspect actual production BODY, frozen exact header/context, actual compiled marker/public full generic application/axioms, direct compiled VALUE Mathlib byparts parent, actual native fence/header-token scan and unchanged fingerprint. Review the proof algebra rather than trusting green exit or worker summaries. Compare operative source-card-v2 and retraction with pinned original source; the original /2-missing claim was false, rejected and withdrawn. No new erratum is proposed. The potential generalization admits zero/stalled weights, signed a,C, unbounded aT and T>0. Parent causal OSD remains required-draft and no consumer-only or algorithm closure may be inferred.

Separately review BOTH FULL canary conjunctions and four concrete definitions against the neutral decode, including strict-gap route via the same public lemma at C3, leading zero/stall/rising potential, nonempty allzero weights with negative C, and T1 with terminal above C and negative RHS. Four selected public calls required later; they do not prove necessity/full graph. The type probe elaborates propositions only; NO Test BODY exists. If favorable, authorize create-only Tests/OnlineAdaptivePotentialCanary.lean with exact context, two headers and proof bodies, no Test-root/public-root/reader/pin/old source edits. Separate canary BODY and whole adaptive package gates remain required. Do not call this leaf or package accepted by full harness. Actor/model/medium history limits explicit; no independent human/external/runtime attestation.

Write create-only potential-BODY-and-canary-CONTRACT-review-v1.md/.json in this RUN, UTF8 single LF, with source/statement/BODY/canary-contract separate verdicts, all seven slots, RAW before/expected/after rows and manifest/report SHA, complete required repairs or exact allowed window. No files outside those two reports may change. Total Goal active.
''')
print('Fixed bounded review packet created.', flush=True)
