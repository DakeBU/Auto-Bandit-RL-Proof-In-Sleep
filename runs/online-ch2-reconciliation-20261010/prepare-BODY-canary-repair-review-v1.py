from generic_ftl_proof import *

fixed()
check_context()
canary = LEAF / 'canary-v2'
neutral = RUN / 'neutral-finite-selector-canary-reconstruction-v2.json'
assert sha(neutral) == 'e1fd928df8ac5a4722c0aee7b8fac1068028cd7fb1ac0630ac0e9a81ea1d1427'
assert sha(RUN / 'neutral-finite-selector-canary-reconstruction-v2.md') == '67e319db91affe7faeb62aee6730919f98f965b03ce5ea58da944d934f04e12b'
assert sha(RUN / 'NeutralFiniteSelectorCanaryPacketV2.lean') == '2981cec41d6e3eaaf917133f22b471e0faa8e9616b3370879a85275b3c508b18'
write(RUN / '30_worker-generic-ftl-BODY-v1.md', '''# Formalizer worker output: frozen generic FTL BODY

The same formalizer records this output after the actual attempts. Director/architect intent is the already reviewed generic-ftl-v1 contract and dependency DAG; this is not an independent review or an invented earlier timestamp.

The four exact definitions/imports and all nine exact public headers are unchanged. First select_some_spec compiled, then the dependency-ready select_none_iff/cumulative_prefix/select_congr/predict_zero compiled. Only after those parents did uniqueness and the three prediction terminals close. There are nine actual public theorem bodies and zero private helpers in the new module. This closes the encoded generic conditional selector foundation, not nine printed book results or any performance bound.

select_congr constructs equality of the full minimizer sets using restricted cumulative equality, then rewrites the exact set-based classical selector. It does not identify arbitrary tied minimizers. predict_some_spec and predict_none_iff include the actual zero-time initialization; predict_prefix excludes current/future losses and outside-domain values. Failure is per-prefix, not absorbing recursion.

One actual production compiler failure occurred in the zero-time failure implication: simplification of an impossible Option equality was not itself a proof of the negated minimum existential. Version2 constructs and eliminates the impossible some=none equality. The failed RAW source and compiler output remain retained; no terminal was weakened. Canary draft1 separately failed to synthesize membership decidability in a real-set if. Canary draft2 adds local classical only, preserving all eight terminal headers and prior failure evidence.

Focused lake build genuinely reports Built BanditRLProof.OnlineFTLSelector and Build completed successfully (960 jobs). Public checks resolve all thirteen values; #print axioms reports only propext/Classical.choice/Quot.sound. Actual compiled direct TYPE_VALUE extraction covers thirteen FTL values and thirty-one prescient parent/source values. These are not root/Tests/full harness gates, a complete transitive graph or a source coverage denominator.

Eight Test propositions and complete concrete contexts elaborate in production and renamed neutral probes. Distinct neutral reconstruction is complete. No Test BODY/root import, source-model repair acceptance, registry/reader change, chapter completion or Goal completion is inferred. All are separate pending gates.
''')
paths = set()
def add(p):
    p = ROOT / p
    assert p.is_file(), p
    paths.add(p)

for p in [ROOT / 'AGENTS.md', ROOT / '.agents/skills/bandit-semantic-roundtrip/SKILL.md',
    ROOT / 'tools/abrl_lifecycle.py', PDF, MODULE]:
    add(p)
for directory in [LEAF, canary]:
    for p in directory.iterdir():
        if p.is_file(): add(p)
for name in [
    'source-model-review-v1.md', 'source-model-review-v1.json',
    'source-model-review-inputs-v1.json',
    'generic-ftl-contract-review-v1.md', 'generic-ftl-contract-review-v1.json',
    'generic-ftl-contract-review-inputs-v1.json',
    'generic-ftl-production-candidate-v1.json', 'generic-ftl-production-value-inspection-v1.json',
    'generic-ftl-production-lake-build-v1.json', 'generic-ftl-public-and-axioms-v1.json',
    'GenericFTLPublicProbeV1.lean', 'generic-ftl-select-some-BODY-v1.json',
    'generic-ftl-ready-parents-BODY-v1.json', 'generic-ftl-prediction-terminals-BODY-v1.json',
    'generic-ftl-prediction-terminals-BODY-v2.json', 'generic-ftl-prediction-repair-v2.json',
    'generic-ftl-canary-type-probe-v1.json', 'generic-ftl-canary-type-probe-v2.json',
    'neutral-finite-selector-canary-type-probe-v2.json',
    'NeutralFiniteSelectorCanaryPacketV2.lean', 'GenericFTLCanaryTypeProbeV2.lean',
    'neutral-finite-selector-canary-reconstruction-v2.md', 'neutral-finite-selector-canary-reconstruction-v2.json',
    'ftl-canary-context-repair-v2.json', '30_worker-generic-ftl-BODY-v1.md',
    'staged-module-delta-resolution-v1.json', 'staged-module-delta-supplement-v1.json',
    'interior-staged-visible-code-delta-v1.diff',
    'definition-and-forward-bindings-execution-v1.json', 'definition-and-forward-bindings-execution-v2.json',
    'definition-and-forward-bindings-execution-v3.json',
    'definition-context-binding-repair-v2.json', 'forward-source-schema-repair-v3.json',
    'reconciliation-selected-value-graph-v1.json', 'reconciliation-selected-values-v1.json',
    'ExportReconciliationValuesV1.lean', 'bind-prescient-chain-command-v1.json',
    'resolve-staged-module-deltas-v1.py', 'complete-staged-deltas-v1.py']:
    add(RUN / name)
for name in ['appropriate-scope-receipt-selection-draft-v1.json',
    'omitted-definition-context-bindings-draft-v1.json', 'required-forward-dependencies-draft-v1.json',
    'prescient-complete-chain-bindings-draft-v1.json', 'domain-structure-signature-repair-v1.json',
    'ancillary-signature-adapter-v1.json']:
    add(CONTRACT / name)
add(ROOT / 'docs/contracts/online-ch2-chapter-audit-v1/complete-source-reconciliation-draft-v3.json')

# Exact original page anchors; no new attribution is inferred from example counts.
for page in [23, 24]:
    for suffix in ['-text-v1.txt', '-v1.png']:
        add(ROOT / 'runs/online-ch2-chapter-audit-20261009' / ('source-pdf' + str(page) + suffix))

def collect_exact_paths(value):
    if isinstance(value, dict):
        for k, v in value.items():
            if k in ['path', 'staged_receipt', 'module'] and isinstance(v, str):
                p = ROOT / v
                if p.is_file(): add(p)
            elif k not in ['semantic_scope', 'raw_input_checks']:
                collect_exact_paths(v)
    elif isinstance(value, list):
        for v in value: collect_exact_paths(v)

for name in ['staged-module-delta-resolution-v1.json', 'staged-module-delta-supplement-v1.json']:
    collect_exact_paths(load(RUN / name))
for name in ['omitted-definition-context-bindings-draft-v1.json', 'prescient-complete-chain-bindings-draft-v1.json']:
    collect_exact_paths(load(CONTRACT / name))
for p in (RUN / 'snapshots').glob('generic-ftl-*.lean.raw'): add(p)
write(RUN / 'production-BODY-canary-CONTRACT-repair-review-inputs-v1.json', dict(rows=rows(paths),
    scope='Separate verdicts: exact nine production BODY targets; eight canary draft2 CONTRACT targets only; bounded source-model R2/R3/R4 repairs. No Test BODY or chapter FINAL acceptance.',
    outputs=['production-BODY-canary-CONTRACT-repair-review-v1.md', 'production-BODY-canary-CONTRACT-repair-review-v1.json']))
fixed()
print('Review inputs', len(paths), 'manifest SHA', sha(RUN / 'production-BODY-canary-CONTRACT-repair-review-inputs-v1.json'), flush=True)
