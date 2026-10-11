from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash

dpath = RUN/'bootstrap-blind-decoder-v1.json'
assert sha(dpath) == 'f3a1865a3385e80fcbfe52dec746996132fba9c3221f75e94b5b6f78dcc62593'
d = load(dpath)
assert d['inputs_unchanged'] and not d['unresolved_ambiguities']
assert sha(d['report']) == d['report_sha256']
assert sha(d['input_path']) == d['input_sha256']
for r in d['actual_read_files']:
    assert sha(r['path']) == r['sha256_raw_bytes']
f = load(CONTRACT/'bootstrap-fingerprints-draft-v1.json')
assert sha(CONTRACT/'algorithm-definition-context-draft-v2.lean.txt') == f['context_sha256']
for name, row in f['headers'].items():
    assert sha(row['path']) == row['raw_sha256']
    raw = Path(row['path']).read_text(encoding='utf8').rstrip()
    assert raw.endswith(':= by')
    assert statement_hash(raw[:-len(':= by')]) == row['normalized_statement_hash']
assert sha(ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean') == 'd82719a0e0b55a712285e586a2c9bf3bd9eda108a06ac26ba178249aeff74308'
b = load(RUN/'causal-state-BODY-review-v1.json')
assert sha(RUN/'causal-state-BODY-review-v1.json') == '253ec3d2d16f7c46eed0b76259d597674da1ec4ad6972e150a39a71bab7c6bd1'

groups = [
    ['energy_succ', 'output_succ'],
    ['energy_eq_sum', 'history_mem', 'eta_eq_energy'],
    ['output_mem', 'energy_nonneg'],
    ['trajectory_finite_loss', 'oracle_feedback'],
    ['canonical_feedback']]
write(CONTRACT/'bootstrap-contract-draft-v1.md', '''# Same-run bootstrap contract, v1

The exact ten headers and eight-definition context are RAW/statement fingerprinted in bootstrap-fingerprints-draft-v1.json. They are derived interfaces of the already compiled causal recursion, not ten newly claimed book results. Their complete quantifiers and conclusions have a distinct neutral reconstruction. There are no new definitions, new algorithm inputs, gradient/stability assumptions, loss class weakenings, imports, or terminal alterations. All real alpha,D are allowed here. Initial feasibility is needed precisely for history/output feasibility, finite losses and lawful feedback, and not for energy identities. Total division and zero feedback remain unchanged. Finite losses use properness plus global supports at feasible points, not legality of an arbitrary p. OracleLaw is a stronger all-input sufficient condition; actual-prefix LegalFeedback remains the main parent premise. canonical_feedback uses the existing shared classical selector and its compiled legal law.

Proposed finite window: append ONLY exact ten headers and their BODYs to BanditRLProof/OnlineAdaptiveOSD.lean, preserving every existing byte except moving the final namespace end. No new helper declarations or context changes. Conditional dependency groups: A energy_succ/output_succ; B energy_eq_sum/history_mem/eta_eq_energy; C output_mem/energy_nonneg; D trajectory_finite_loss/oracle_feedback; E canonical_feedback. Each group must have a successful actual focused compiler build before the downstream group is written. If any fails, retain the full failed source/log and repair only BODYs in that group with unchanged headers/context. All source snapshots, public generic applications, axioms, declaration fences and actual compiled VALUE evidence are separate from compilation and semantic review. No parent performance BODY, zero/nonzero-step target, optimized benchmark, canary, root, reader, registry, old library or global SGB window is opened here. The negative-terminal regret_bound stays frozen and required.

Director/architect/formalizer root, distinct reused osd_blind reconstruction and source_reviewer anti-anchored review; requested Astra/medium, no runtime, human, external or absolute-blind attestation. All prior related-history/API-slice limitations remain explicit. This is a dependency lowering within one open causal OSD package, not chapter/Goal acceptance. Full combined publication gates and future actual regret proof remain pending.
''')
write(RUN/'director-bootstrap-v1.md', '''Freeze all ten same-run bootstrap interfaces before BODYs. Preserve the fixed negative-terminal regret endpoint and the algorithm's actual generated state; do not replace a support law with a regret/stability premise. Prefer existing shared projection, proper-support finiteness and canonical lawful-policy APIs. Grouped focused builds lower dependencies inside this package, with failures retained and no extra source-result counting.
''')
write(RUN/'architect-bootstrap-v1.md', '''DAG groups: compiled state_succ -> A energy_succ/output_succ -> B energy_eq_sum/history_mem/eta_eq_energy -> C output_mem/energy_nonneg -> D trajectory_finite_loss/oracle_feedback -> E canonical_feedback. The shared project_spec supplies projection feasibility, finite_loss supplies EReal finiteness from SourceProper/global supports, OracleLaw supplies actual current-history legality, and canonicalPolicy_legal discharges that optional stronger law. Default one lower route; no parallel proof contest or silently added helper declarations. Next zero/nonzero step headers require a separate frozen review window before tactics.
''')
files = [PDF, ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean',
    ROOT/'BanditRLProof/OnlineSubgradientPolicy.lean', ROOT/'BanditRLProof/OnlineSubgradientDescent.lean',
    ROOT/'BanditRLProof/OnlineGradientDescent.lean',
    ROOT/'runs/online-ch2-adaptive-summation-20261010/source-pdf51-v1.png',
    ROOT/'runs/online-ch2-adaptive-summation-20261010/source-pdf52-v1.png']
files += [CONTRACT/n for n in [
    'algorithm-definition-context-draft-v2.lean.txt', 'algorithm-regret_bound-header-draft-v1.lean.txt',
    'algorithm-source-card-draft-v1.md', 'algorithm-assumption-delta-draft-v1.md',
    'algorithm-stabilized-v1.json', 'bootstrap-fingerprints-draft-v1.json',
    'bootstrap-neutral-packet-v1.lean.txt', 'bootstrap-contract-draft-v1.md']]
files += [Path(r['path']) for r in f['headers'].values()]
files += [RUN/n for n in [
    'bootstrap-blind-decoder-v1.md', 'bootstrap-blind-decoder-v1.json',
    'BootstrapTypeProbeV1.lean', 'bootstrap-type-probe-v1.json',
    'causal-state-BODY-review-v1.md', 'causal-state-BODY-review-v1.json',
    'algorithm-CONTRACT-review-v1.md', 'algorithm-CONTRACT-review-v1.json',
    'state-succ-focused-build-v1.json', 'state-prefix-focused-build-v1.json',
    'causal-state-public-probe-v1.json', 'causal-state-values-native-v1.json',
    'director-bootstrap-v1.md', 'architect-bootstrap-v1.md']]
assert all(p.is_file() for p in files)
write(RUN/'bootstrap-CONTRACT-inputs-v1.json', dict(files=rows(files), groups=groups,
    scope='Ten exact same-run bootstrap CONTRACT headers only; no new BODY exists yet.'))
write(RUN/'bootstrap-CONTRACT-packet-v1.md', '''# Anti-anchored bootstrap CONTRACT review

RAW hash all fixed inputs before/after; read actual definitions and compiled causal state BODYs, exact ten complete headers/context/fingerprints, full neutral reconstruction and its limitations, shared API statements and the parent/source cards. Personally verify original PDF51/52 source as relevant; distinguish re-viewed pages from earlier staged viewing. Audit all seven semantic slots and search for mismatch: arbitrary real signs, skip/projection feasibility, Fin(t+1) history indexing, inclusive energy, total division, EReal finiteness without selected legality, all-input OracleLaw versus actual-prefix legality, and existing canonical selector rather than a new chooser. Ten interfaces are not ten source theorem closures. Regret terminal is unchanged and unproved.

If favorable, authorize EXACT append-only ten headers/BODYs in the named five sequential dependency groups, preserving existing prefix and moving only final namespace end. Require actual focused compiler success before each downstream group. No additional context/import/helper/parent/root/Test/registry/publication/global edits. Header/context changes require a new version and review, never a tactic repair. No proof tactic execution requested from reviewer.

Write create-only bootstrap-CONTRACT-review-v1.md/.json UTF8singleLF in this RUN, with complete verdict, all RAW checks, exact header/context/production/index/report hashes, source correspondence and explicit deltas, conditional finite edit window or blocking repairs, and remaining full-package gates. Disclose distinct reused staged actor, no runtime/human/external/absolute-blind attestation. Goal remains active; contract approval is not proof/acceptance.
''')
print('Decoder RAWs and all exact headers checked; bootstrap CONTRACT packet ready.', flush=True)
