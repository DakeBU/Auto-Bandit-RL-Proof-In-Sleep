from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash
for name, expected in [
    ('algorithm-blind-decoder-v1.json','355f3ef00df7ac2bcbe5f0445f0c13f2e1af3b85a06d0389678c695d476989c1'),
    ('algorithm-prefix-blind-decoder-v1.json','4663a6733c830c6133a4ef7c6256b0cd0735a0ecfdc5bd6b69a66e78f2418b11')]:
    p = RUN/name
    assert sha(p) == expected
    d = load(p)
    assert d['inputs_unchanged']
    assert sha(d['report']) == d['report_sha256']
    assert sha(d['input_path']) == d['input_sha256']
    for r in d.get('actual_read_files', []):
        assert sha(r['path']) == r['sha256_raw_bytes']
hashes = {}
for name in ['state_succ','state_prefix','regret_bound']:
    p = CONTRACT/('algorithm-'+name+'-header-draft-v1.lean.txt')
    raw = p.read_text(encoding='utf8')
    assert raw.rstrip().endswith(':= by')
    hashes[name] = dict(path=p.as_posix(), raw_sha256=sha(p),
        normalized_statement_hash=statement_hash(raw.rstrip()[:-len(':= by')]))
write(CONTRACT/'algorithm-fingerprints-draft-v1.json', dict(
    definition_context_sha256=sha(CONTRACT/'algorithm-definition-context-draft-v2.lean.txt'),
    headers=hashes, definition_count=8,
    proof_window_requested=['state_succ','state_prefix after actual state_succ focused build'],
    parent_regret_BODY='not authorized until dependencies ready; frozen terminal only',
    status='draft pending distinct source review'))
write(CONTRACT/'algorithm-contract-draft-v1.md', '''# Exact causal adaptive OSD contract, v1

Operative complete definition contextv2 and exact state_succ/state_prefix/regret_bound headersv1 are fingerprinted in algorithm-fingerprints-draft-v1.json. All8definitions are supplied actual recursive expressions, not axioms. Parent endpoint is a fully specified proposition, still unproved. See source card and assumption delta for all objects, finite-Euclidean geometry, proper/source support semantics, same trajectory, indexing and nonnegative diameter/positive alpha/arbitrary T regimes. Positive or zero energy, D0, T0 all retained. The separate favorable mathematical min/infimum repair is not a compiled benchmark or author endorsement. The earlier incorrect /2 repair stays rejected/withdrawn.

Structural causality must be proved at the whole history×energy state level under equality of complete strict-past loss functions and COMMON fixed V,alpha,D,x1,p; no exogenous eta equality premise. The policy type sees only finite past losses/actions and the current whole loss for feedback. No promise is made for a family reselecting external parameters or policy using a horizon/comparator/future stream. An arbitrary p can encode outside information; the exact fixed-policy prefix theorem, and later the shared canonical lawful current-loss policy adapter, define the honest algorithmic boundary. Main performance quantifies every actual-prefix legal p, no off-path OracleLaw premise; that stronger shared law is an optional sufficient adapter to be derived. No consumer-only assumption of regret/stability is allowed.

Proposed finite lower window after favorable CONTRACT review: create-only BanditRLProof/OnlineAdaptiveOSD.lean with EXACT contextv2, state_succ exact header/BODY, focused compile; only then append exact state_prefix header/BODY and focused compile. Prefix may use the actual compiled state_succ; no other public declaration/body or altered context is allowed yet. Parent regret_bound stays frozen in CONTRACT, absent from production until energy/feasibility/finite-support/one-step/zero-cases dependencies ready. Future headers must be reviewed before their bodies. No root/Tests/reader/registry/pin/old library/global frontier edits are requested. OWN lifecycle and evidence files may record actual stages, failures and local frontier.

Director/architect/formalizer root; reused distinct osd_blind reconstructs complete8definitions+2targets and supplemental exact fixed-policy prefix. API slice incident/hash timing is disclosed in decoder report; no absolute blindness or runtime/human/external attestation. Reviewer searches for mismatch in source/semantics/recurrence/parent constants and this honest information boundary before opening proof window. Default one lower route, no parallel proof contest. Current potential dependency BODY/canary reviewed/compiled locally, old energy dependency exact OPEN draft PR217, current full combined/publication gates pending. Whole Goal active.
''')
write(RUN/'director-algorithm-v1.md', '''Freeze one causal parent, not an exogenous future-energy schedule. Preserve exact source terminal and all degenerate regimes. First finite leaves joint state recurrence and strict-past whole-state identity; parent bound is fixed but proof not started. Eight definitions share canonical Domain/projection/SupportPolicy/source supports; no per-Book library. Record distinct semantic rounds and failures, all later combined gates separately.
''')
write(RUN/'architect-algorithm-v1.md', '''DAG: shared Domain/projection/support semantics -> exact joint Nat.rec definitions -> state_succ -> state_prefix; definitions/state_succ -> energy recurrence/energy sum/nonnegativity and feasible histories -> proper finite losses/legal actual support -> zero skip and actual nonzero projection one-step. Same-run one-step -> generic zero-weight potential + existing energy sum bound -> all-T/nonnegative-D parameterized negative-terminal parent -> alpha1 Eq4.4 / alpha sqrt2/2 Theorem4.14. Independent positive-eta benchmark uses shared OnlineOptimalStep APIs and the separately reviewed source reconciliation. Only first two proof leaves requested now; no other BODY or global edits. Prefix algebra uses equal strict-past function tuples and same state to rewrite next support, inclusive energy and update. No tactic pivot planned.
''')
files = [PDF, PUBLIC, ROOT/'Tests/OnlineAdaptivePotentialCanary.lean',
    ROOT/'BanditRLProof/OnlineSubgradientPolicy.lean', ROOT/'BanditRLProof/OnlineSubgradientDescent.lean',
    ROOT/'BanditRLProof/OnlineGradientDescent.lean', ROOT/'BanditRLProof/OnlineAdaptiveEnergy.lean',
    ROOT/'runs/online-ch2-adaptive-summation-20261010/source-pdf51-v1.png',
    ROOT/'runs/online-ch2-adaptive-summation-20261010/source-pdf52-v1.png',
    ROOT/'conversion-windows'/(TASK+'.md'), ROOT/'proof-obligations'/(TASK+'.md')]
files += [CONTRACT/n for n in [
    'algorithm-definition-context-draft-v1.lean.txt', 'algorithm-definition-context-draft-v2.lean.txt',
    'algorithm-state_succ-header-draft-v1.lean.txt', 'algorithm-state_prefix-header-draft-v1.lean.txt',
    'algorithm-regret_bound-header-draft-v1.lean.txt', 'algorithm-neutral-packet-v1.lean.txt',
    'algorithm-prefix-neutral-v1.lean.txt', 'algorithm-neutral-renaming-v1.json',
    'algorithm-source-card-draft-v1.md', 'algorithm-assumption-delta-draft-v1.md',
    'algorithm-fingerprints-draft-v1.json', 'algorithm-contract-draft-v1.md',
    'algorithm-terminal-draft-v1.md', 'minimum-infimum-repair-proposed-v1.md']]
files += [RUN/n for n in [
    'director-algorithm-v1.md', 'architect-algorithm-v1.md',
    'algorithm-blind-decoder-v1.md', 'algorithm-blind-decoder-v1.json',
    'algorithm-prefix-blind-decoder-v1.md', 'algorithm-prefix-blind-decoder-v1.json',
    'AlgorithmDraftTypeProbeV1.lean', 'AlgorithmDraftTypeProbeV2.lean', 'AlgorithmPrefixTypeProbeV1.lean',
    'algorithm-draft-type-probe-v1.json', 'algorithm-draft-type-probe-v2.json',
    'algorithm-draft-context-repair-v2.json', 'algorithm-prefix-type-probe-v1.json',
    'algorithm-prefix-API-retrieval-v1.json', 'algorithm-optimum-API-retrieval-v1.json',
    'potential-BODY-and-canary-CONTRACT-review-v1.md', 'potential-BODY-and-canary-CONTRACT-review-v1.json',
    'potential-canary-BODY-minimum-review-v1.md', 'potential-canary-BODY-minimum-review-v1.json',
    'potential-focused-build-v1.json', 'potential-canary-focused-build-v2.json']]
assert all(p.is_file() for p in files)
write(RUN/'algorithm-CONTRACT-inputs-v1.json', dict(files=rows(files),
    scope='Bounded algorithm definition/recurrence/prefix/fixed parent terminal CONTRACT review only; no compiled algorithm/performance claim.'))
write(RUN/'algorithm-CONTRACT-packet-v1.md', '''# Anti-anchored causal algorithm CONTRACT review

Independently RAW hash every fixed input before/after. Read complete8recursive definitions, three exact headers/fingerprints, BOTH neutral decoder reports/context and disclosed slice/hash-timing incident, proper/source support shared types, original PDF51/52, separate source minimum repair decision. Search for mismatch in all seven slots, hidden circular dependence, future/horizon/comparator inputs, zero skip after positive energy, current action/feedback order, inclusive energy, actual-prefix legality vs optional lawful oracle, toReal finiteness, missing source convexity/generalized support sufficiency, negative terminal constants, all T/D0/zeroenergy cases. Audit fixed common external parameters/closures limit: no absolute causality for reselected p or D, but exact strict-past whole-state prefix target is required and no external eta premise is allowed. Do not approve arbitrary whole-future algorithm existence in place of the displayed Nat.rec.

If favorable stabilize EXACT contextv2 and all3terminal headers, authorize only create-only BanditRLProof/OnlineAdaptiveOSD.lean with8definitions plus state_succ BODY and focused build; then exact state_prefix BODY ONLY AFTER successful state_succ actual focused build. Parent regret_bound remains a frozen required terminal, no BODY allowed yet. No other library/publicroot/Testroot/registry/reader/pin/global edits. Compile markers distinguish scratch definitions/Prop TYPE from proof. Decide source deltas explicitly; reject if terminal or information contract mismatches. The separate min/infimum mathematical approval does not certify a new IsGLB theorem. No algorithm accepted/compiled yet, no package/chapter/Goal closure.

Write create-only algorithm-CONTRACT-review-v1.md/.json in this RUN, UTF8singleLF, separate context/recurrence/prefix/parent-terminal/source verdicts, seven slots, full blocking repairs or precise conditional edit window, all RAW checks, manifest/report/context/header hashes. Disclose reused staged actor/history and no human/external/runtime attestation. Do not edit other files or run tactics.
''')
event('potential-candidate-event-v1', 'candidate', dict(
    current_leaf='weighted_potential_sum', statement_hash=load(CONTRACT/'potential-stabilized-v2.json')['statement_hash'],
    production_BODY_review=sha(RUN/'potential-BODY-and-canary-CONTRACT-review-v1.json'),
    full_canary_BODY_review=sha(RUN/'potential-canary-BODY-minimum-review-v1.json'),
    state='compiled-local semantic-reviewed dependency candidate',
    combined_gate='pending current adaptive package', package_accepted=False, parent_causal_OSD='required-draft'))
event('algorithm-draft-event-v1', 'draft', dict(
    current_leaf='state_succ', exact_context=sha(CONTRACT/'algorithm-definition-context-draft-v2.lean.txt'),
    parent_terminal_hash=hashes['regret_bound']['normalized_statement_hash'],
    context_and_header_contract='pending review', BODY='not created', whole_Goal='active'))
print('Exact causal contract review packet and truthful dependency candidate/draft events recorded.', flush=True)
