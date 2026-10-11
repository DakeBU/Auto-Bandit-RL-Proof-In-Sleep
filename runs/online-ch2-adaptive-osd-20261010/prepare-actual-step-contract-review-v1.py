from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash
decoder_path = RUN/'actual-step-blind-decoder-v1.json'
assert sha(decoder_path) == '70c9022c08219a7520d0fb24ea9642056c3c42fdfb353c3ed5853b239635ca27'
d = load(decoder_path)
assert d['inputs_unchanged'] and not d['unresolved_ambiguities']
assert sha(d['report']) == d['report_sha256']
for row in d['actual_read_files']:
    assert sha(row['path']) == row['sha256_raw_bytes']
assert d['conjunction_counts'] == {'certificate_4':2, 'certificate_5':2, 'certificate_7':2}
bpath = RUN/'bootstrap-BODY-review-v1.json'
assert sha(bpath) == '4496c4caeda764e7abfeb2f87d4e7ea00a851852b24b42e0ca22f91101eed6b6'
b = load(bpath)
assert not b['required_repairs']
for row in b['raw_input_checks']:
    assert sha(row['path']) == row['expected_sha256'] == row['before_sha256'] == row['after_sha256']
assert sha(b['report']) == b['report_sha256']
f = load(CONTRACT/'actual-step-fingerprints-draft-v1.json')
for row in f['headers'].values():
    assert sha(row['path']) == row['raw_sha256']
    raw = Path(row['path']).read_text(encoding='utf8').rstrip()
    assert statement_hash(raw[:-len(':= by')]) == row['normalized_statement_hash']
assert sha(CONTRACT/'algorithm-regret_bound-header-draft-v1.lean.txt') == f['parent_regret_header_sha256']
assert load(RUN/'actual-step-type-probe-v1.json')['actual_exit'] == 0
assert load(RUN/'actual-step-API-probe-v1.json')['actual_exit'] == 0
groups = [
    ['energy_step_mono', 'energy_pos_of_selected_ne_zero'],
    ['eta_pos_of_selected_ne_zero', 'zero_feedback_step', 'regret_zero_diameter'],
    ['one_step_chain'], ['one_step']]
write(CONTRACT/'actual-step-contract-draft-v1.md', '''# Actual step CONTRACT, v1

Seven complete headers, unchanged eight-definition context, same frozen negative-terminal parent, and full neutral decoder are bound in the fingerprints/input manifest. The decoder correctly reconstructs THREE two-conjunct conclusions (zero_feedback_step, one_step_chain, regret_zero_diameter); root's decoder request informally said two, but exact packet contained all three and was unchanged. No theorem BODY or new helper/import/context is supplied yet. Same-run current legal support, current proper/subdifferentiable loss and feasible comparator suffice locally, without imposing feasible x1 where not mathematically needed. Zero-diameter helper explicitly DOES retain feasible x1 and u, and asserts only totalized real regret equality and terminal distance, not EReal finiteness or support legality.

Conditional window requested: append exactly these seven headers/BODYs to current OnlineAdaptiveOSD.lean, preserving all current bytes except moving final namespace end. Groups A energy_step_mono/energy_pos_of_selected_ne_zero; B eta_pos_of_selected_ne_zero/zero_feedback_step/regret_zero_diameter; C one_step_chain; D one_step. Actual focused build of each group must succeed before any downstream group is written. No other declaration, import/context, parent regret, benchmark, canary/root/registry/publication/global edits. BODY repairs stay within failed group with retained source/log and unchanged frozen headers. Source/card/delta mathematics and primitive projected-chain API are independently reviewed before tactics.

DAG: compiled energy_succ/nonneg -> monotonicity and nonzero inclusive positivity -> eta positivity; compiled output_succ plus shared lemma_2_31 support component -> zero skip and nonpositive gap; compiled output_mem plus diameter0 -> equal points/zero real regret and norm; eta positivity/shared full lemma_2_31 and actual nonzero output branch -> full two-part one_step_chain; zero branch plus nonzero chain/algebra -> all-feedback weighted one_step. These close dependencies for the exact fixed parent, without accepting a desired stability/regret bound as a premise. One lower route; no parallel tactic search. Support_gap was found and typed, but its two-line shared lemma_2_31 adapter does not justify a new linear-policy import/context change.

Root personally viewed original cached PDF31 pixels at original detail in this drafting round (Lemma2.31 allows arbitrary supported ambient current point); source reviewer independently audits correspondence and states page reuse/fresh view precisely. PDF51/52 source proof and explicit zero-skip remain operative, original minimum separately reviewed and not silently changed. Parent retains all T,D>=0/zeroenergy; local D>0 case is only one branch. No source/chapter/Goal acceptance, no runtime/human/external/absolute-blind attestation.
''')
write(RUN/'director-actual-step-v1.md', '''Lower from actual causal state/feasibility to its legal support and projection one-step. Preserve explicit skip when current support is zero, including after positive energy. Maintain source finite-loss meaning; no future-energy oracle or desired performance premise. All seven headers have full neutral reconstruction, including three complete conjunctive conclusions; parent unchanged and required.
''')
write(RUN/'architect-actual-step-v1.md', '''Four conditional groups A energy monotonicity/positive inclusive energy, B eta positivity/zero feedback/zero diameter, C actual two-part nonzero projected chain, D all-feedback weighted inequality. Shared lemma_2_31 gives both exact support and projection inequalities; zero branch consumes only its eta1 first component, not a stability assumption. Current support finiteness does not require initial feasibility. D0 separate same-point argument consumes actual output_mem. Subsequent sum uses weighted potential and energy bound, but no parent BODY window requested yet.
''')
files = [PDF, ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean',
    ROOT/'BanditRLProof/OnlineSubgradientDescent.lean', ROOT/'BanditRLProof/OnlineSubgradientPolicy.lean',
    ROOT/'BanditRLProof/OnlineLinearization.lean', ROOT/'BanditRLProof/OnlineGradientDescent.lean',
    ROOT/'runs/online-ch2-chapter-audit-20261009/source-pdf31-v1.png',
    ROOT/'runs/online-ch2-chapter-audit-20261009/source-pdf31-text-v1.txt',
    ROOT/'runs/online-ch2-adaptive-summation-20261010/source-pdf51-v1.png',
    ROOT/'runs/online-ch2-adaptive-summation-20261010/source-pdf52-v1.png']
files += [Path(row['path']) for row in f['headers'].values()]
files += [CONTRACT/n for n in [
    'algorithm-definition-context-draft-v2.lean.txt', 'algorithm-regret_bound-header-draft-v1.lean.txt',
    'algorithm-assumption-delta-draft-v1.md', 'algorithm-source-card-draft-v1.md',
    'actual-step-fingerprints-draft-v1.json', 'actual-step-source-card-draft-v1.md',
    'actual-step-contract-draft-v1.md', 'actual-step-neutral-packet-v1.lean.txt']]
files += [RUN/n for n in [
    'bootstrap-BODY-review-v1.md', 'bootstrap-BODY-review-v1.json',
    'actual-step-blind-decoder-v1.md', 'actual-step-blind-decoder-v1.json',
    'ActualStepTypeProbeV1.lean', 'actual-step-type-probe-v1.json',
    'ActualStepAPIProbeV1.lean', 'actual-step-API-probe-v1.json',
    'actual-step-source-API-window-v1.json', 'actual-step-memory-retrieval-v1.json',
    'actual-step-retrieval-record-v1.json', 'actual-step-retrieval-native-RAW-v1.jsonl',
    'director-actual-step-v1.md', 'architect-actual-step-v1.md']]
files += [RUN/('actual-step-declaration-retrieval-%d-v1.json'%i) for i in range(1,5)]
assert all(p.is_file() for p in files)
write(RUN/'actual-step-CONTRACT-inputs-v1.json', dict(files=rows(files), groups=groups,
    scope='Seven frozen same-run one-step dependency headers, not compiled BODYs/performance.'))
write(RUN/'actual-step-CONTRACT-packet-v1.md', '''# Anti-anchored actual-step CONTRACT review

Independently RAW hash all fixed inputs before/after. Read all seven exact headers, eight definitions, full neutral reconstruction (all THREE conjunctions), full type/API probes and actual compiled bootstrap dependencies, exact unchanged parent, source/card/deltas and original PDF31/51/52 as relevant. Audit missing initial membership in local supported-point statements versus necessary membership for zero diameter, global support/SourceProper finite loss, alpha/D sign branches, inclusive energy positivity, total division, zero feedback after positive energy, actual projection branch and both scaled chain inequalities. Reject any mismatch in seven slots, hidden future/exogenous eta, supplied desired regret/stability premise, source convexity-equivalence overclaim, or dropped D0/zeroenergy/T0 parent case.

If favorable approve only exact seven headers/BODYs in A→D sequential dependency groups with actual focused success prerequisite before downstream production append. Preserve whole existing source prefix except moved final namespace end. No helper/import/context/parent/benchmark/canary/root/reader/registry/global edits. This is dependency lowering within the open causal package. No tactics/build requested from reviewer.

Create-only actual-step-CONTRACT-review-v1.md/.json UTF8singleLF in this RUN: all RAW/index/report/context/header/production hashes, seven-slot verdicts/source deltas, precise finite conditional edit window or blocking repairs, personally viewed/reused source-image disclosure and staged actor limits. No human/external/runtime/absolute-blind claims or package/chapter/Goal closure.
''')
event('bootstrap-candidate-event-v1', 'candidate', dict(current_leaf='canonical_feedback',
    BODY_review_sha256=sha(bpath), local_state='compiled and distinct semantic BODY-reviewed',
    source_results_count='not ten book results', full_package_gate='pending', parent_regret='required open'))
event('actual-step-draft-event-v1', 'draft', dict(current_leaf='energy_step_mono',
    exact_headers=f['headers'], parent_regret_hash=f['parent_regret_header_sha256'],
    BODY='not written', contract_review='pending', whole_Goal='active'))
print('Exact actual-step CONTRACT packet ready; bootstrap candidate and next draft recorded.', flush=True)
