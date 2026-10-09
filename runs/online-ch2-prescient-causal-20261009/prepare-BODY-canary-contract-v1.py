from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
TEST = ROOT / 'Tests/OnlinePrescientBregmanCanary.lean'
assert not TEST.exists()
assert load(RUN / 'transition-inspected-v2.json')['production_sha256'] == sha(PUBLIC)
assert load(RUN / 'production-dependency-inspected-v2.json')['production_sha256'] == sha(PUBLIC)
assert (RUN / 'canary-blind-v1.md').exists() and (RUN / 'canary-blind-v1.json').exists()
assert (RUN / 'canary-blind-context-resolution-v1.md').exists()
assert (RUN / 'canary-blind-context-resolution-v1.json').exists()
d = load(CONTRACT / 'stabilized-v1.json')
for t in d['targets']:
    assert statement_hash(lean_declaration_header(PUBLIC, t['declaration'])) == t['statement_hash']
neutral = RUN / 'canary-neutral-types-v1.txt'
text = neutral.read_text(encoding='utf8')
targets = []
for short in ['two_distinct_current_losses', 'boundary_outside_center_run',
              'closed_strict_regularizer_missing_minimum', 'interior_extension_boundary_difference']:
    tail = 'theorem ' + short + text.split('theorem ' + short, 1)[1]
    ends = [i for i in [tail.find('\n\ntheorem '), tail.find('\n\nend ')] if i >= 0]
    header = tail[:min(ends)]
    targets.append(dict(declaration='BanditRL.OnlinePrescientBregmanCanary.' + short,
        exact_proposed_header=header, statement_hash=statement_hash(header),
        header_raw_sha256=hashlib.sha256(header.encode('utf8')).hexdigest(),
        statement_hash_convention='native normalized, raw UTF8 header SHA separately bound',
        file=TEST.relative_to(ROOT).as_posix(), context='scalar real, all instances fixed; local let definitions included in the complete header'))
write(CONTRACT / 'canary-targets-draft-v1.json', dict(stage='draft', targets=targets,
    neutral_sha256=sha(neutral), blind_md_sha256=sha(RUN / 'canary-blind-v1.md'),
    blind_json_sha256=sha(RUN / 'canary-blind-v1.json'), test_body_absent=True,
    neutral_context_supplement_sha256=sha(RUN / 'canary-neutral-context-supplement-v1.txt'),
    blind_context_resolution_md_sha256=sha(RUN / 'canary-blind-context-resolution-v1.md'),
    blind_context_resolution_json_sha256=sha(RUN / 'canary-blind-context-resolution-v1.json'),
    proof_plan='Only local have/let helpers, no new named production or Test definitions. Compute actual Choice-selected states by genuine attained minima plus uniqueness; use current public specifications/conditional completion/successor extraction/prefix and same-produced-transition one-step. Both final numeric run bounds retain that actual one-step proof through equality transport. Exponential example proves source regularizer closedness/strictness/global differentiability, proper supported affine loss, actual no feasible min and absorbing none. Extension example invokes new locality for interior equality and proves unequal boundary total-fderiv values; no source boundary derivative validity or selector invariance inferred.',
    source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
snapshot = {r['path']: r for r in load(RUN / 'pre-stabilization-exact-own-metadata-v1.json')['rows']}
changes = []
for row in load(RUN / 'contract-review-inputs-v1.json')['rows']:
    if sha(row['path']) != row['sha256']:
        old = snapshot[row['path']]
        assert old['sha256'] == row['sha256']
        assert hashlib.sha256(base64.b64decode(old['raw_base64'])).hexdigest() == row['sha256']
        changes.append(dict(path=row['path'], historical_sha256=row['sha256'],
            current_sha256=sha(row['path']), exact_RAW_snapshot='pre-stabilization-exact-own-metadata-v1.json',
            reason='Only explicitly approved OWN draft-to-stabilized/proving metadata suffix.'))
assert len(changes) == 3
write(RUN / 'BODY-historical-binding-resolution-v1.json', dict(changed_live_rows=changes,
    all_other_original_source_contract_inputs_unchanged=True, not_false_current_RAW_claim=True))
write(RUN / 'proof-obligations-proving-v1.json', dict(stage='proving',
    production=[dict(declaration=t['declaration'], statement_hash=t['statement_hash'],
        status='focused-compiled/public-VALUE/standard-axioms/fence-backed; BODY-pending') for t in d['targets']],
    exact_definitions=d['definitions'], canaries=[dict(declaration=t['declaration'], status='draft/exact-contract-review-pending') for t in targets],
    required_open=['source-domain/interior hypothesis transport into actual produced run',
        'same-run sharp fixed-step cumulative terminal including source main-text exercise',
        'same-run variable-step cumulative terminal', 'all eight Chapter2 forwarded source containers',
        'combined root/Tests/harness', 'reader/shared-registry/site/semantic-FINAL/native/delivery'],
    package_accepted=False, source_container_closed=False, chapter_proof_total=None,
    chapter_complete=False, whole_Goal_status='ACTIVE'))
write(RUN / 'memory-digest-proving-v1.md', '''Eight frozen proof bodies and two exact definitions focused-compiled. Locality first v1 failed (Filter parameter order/Eventually typing), repaired v2; current-minimum specs v1 failed (automatic impossible-branch closure and coercion-distributing simp), v2 failed (inline tactic tuple parse), repaired v3; four causal/definedness proofs first pass; last one-step v1 failed because an extra inherited NormedSpace conflicted with frozen InnerProductSpace, v2 restores the exact frozen context by closing/reopening namespace, proof body unchanged. Actual failure stdout/result/snapshots and native repair events retained. No semantic target weakening, extra public helper or warning suppression. Eight full generic public VALUEs/standard-only axioms and native frozen guards have separate actual evidence. Selected compiled graph10canonicalnodes/467coalesced direct TYPE_VALUE presences/six required actualVALUE pairs, not a full/transitive/source/registry denominator. Both definitions noncomputable partial mathematical choice; no universal attainment/executable solver/measurable selection claim. Four complete concrete Test targets independently reconstructed but BODYs absent; source review and all acceptance/publication gates pending. Full source interior/attainment/cumulative terminals/all8forwards remain REQUIREDOPEN; whole Chapters1-16 Goal ACTIVE. No main/live update.
''')
write(RUN / 'BODY-canary-contract-review-packet-v1.md', '''# Eight production BODYs and four complete canary CONTRACTs

Independently run common.fixed and verify all current indexed RAW plus2955protected baseline before/after. Original CONTRACT input changes exactly3OWN metadata resolved through immutable RAW snapshots; historical hashes not falsely claimed current. Read pinned source first: sourceX times interiorX; current full loss received before prediction; source theorem explicitly assumes generated interior points, no blanket argmin attainment. Exact8headers/two whole definitions/context are frozen; all8 actual proof bodies present and focused-compiled, eight complete generic public VALUEs, standard-only public/kernel axiom outputs, eight native statement fences/safechecks0. Production actual final context printed: NormedAddCommGroup/InnerProductSpace/CompleteSpace, no extra independent NormedSpace. Other7 use real NormedSpace, no completeness. Actual compiled selected graph10canonicalnodes/467coalesced direct TYPE_VALUE presences/six requiredVALUEpairs; inspect not just imports. Body failures/raw snapshots preserved as memory digest explains; context repair restores frozen scope, no theorem weakening.

BODY inspect: locality uses interior neighborhood eventual equality then actual fderiv congruence/values; no regularity/source boundary validity invented. advance exactly current-only real-eta EReal-objective feasible-min guard/Choice/none. Success spec genuine choose_spec, none iff exact no feasible min. Iterate state0 some x0, current bind. Prefix induction consumes losses/eta below t only, state(t+1) is played round t+1. Successor extracts actual prior some-state and same advance min. None absorbing. Completion is conditional actual per-reached-state local attainment, not future oracle or desired regret. Last proof recovers actual prior witness, identifies it with hx then invokes accepted extended producer; actual properness/global supports/positiveeta/both derivatives preserved with both negative residuals. EmptyV/improper loss/allrealeta only generic specs; source performance restricts hypotheses. Initial center outsideV/lossdomain allowed. No complete source run/interiority guarantee/cumulative endpoint accepted.

Four COMPLETE new Testheaders before BODYs, current neutraldecoder inputs/reconstruction bound. The initial decoder explicitly left SourceClosed unresolved. A separately bound exact neutral predicate supplement and distinct decoder resolution supply its all-real closed-sublevel definition; headers unchanged and original report retained. A: restricted absolute then different restricted affine -5z/8 on[-1,1], nonquadraticpsi=z^4/4+z^2/2, actual Choice-selected states1/2->0->1/2, properness/global supports/strictpsi/nonsmoothabs/topoutside, prefix invariance of both actuallosses under arbitrary future, two nonzero asymmetric movements11/64 and9/64. Universal two-round signed sum retains comparator first/base second and both movements, final -1/2<=-5/16 derived from that actual same-run bound by Eq.mp, not norm_num proof. Plan actual completion from two attained minima then actual successor+uniqueness, no desired outputs assumed.
B: restrictedlinear[0,1]/quadraticpsi, oldcenter-1outsideVANDlossdomain, actual chosen boundary0/movement1/2/universaloneStep/numeric-1/2<=1/2 also derives from actual new transition via Eq.mp. Reuse exact accepted static oldcanaries for genuine min/strictness/properness/supports only; new actual selection and transition derived.
C: V=Iic0 proper subset of X=R, sourceclosed/strict exp regularizer and all actual derivatives, x0=0interiorX andinV, proper globalaffine f=z/global supports, objective expz-1, no attained min via p-1, exact advance none and recursion none forever. No false claim of a complete generated source run or source erratum; theorem source performance is conditional on valid updates. Actual missing-min characterization exercised.
D: X=Ici0, psi=z^2+z,phi=z^2+absz, EqOnX/differoutside; base1interior/target2inX, actual newlocality equality andvalue1. Boundarybase0 yields distinct total-fderiv values4vs6, phi actually nondifferentiable there. No sourceBregmanvalidity atboundary or extension-selector invariance; this audits why interior premise cannot be dropped.

Create-only BODY-canary-contract-review-v1.md/json with report/input/source hashes, before/after rows, seven semantic slots, BODY verdict, canary CONTRACT verdict, overall verdict/required_repairs and exact allowedTest scope if accepted. No Testbody currently, no source/reader/root/native edits by reviewer. Distinct reused staged automated source role requested Astra/medium, history exposure disclosed, no external/human/absolute-blind/runtime attestation. Review is BODY plus TestCONTRACT only; combined/publication/site/FINAL/native/post-native/delivery remain separate. Full source interior/definedness/fixed-variable/all8forward containers remain REQUIREDOPEN; Chapter2partial/denominatornull and whole16GoalACTIVE. No merge/deploy/main/live/CI/Chapter6/15 acceptance.
''')
paths = {p for folder in [RUN, CONTRACT] for p in folder.rglob('*') if p.is_file()
    and '__pycache__' not in p.parts and p.name not in ['trials.jsonl', 'lifecycle-sessions.jsonl', 'lifecycle-state.json', 'own-artifact-journal.md']}
paths.update(Path(row['path']) for row in load(RUN / 'contract-review-inputs-v1.json')['rows'])
paths.update([PUBLIC, ROOT / 'Tests/OnlineBregmanExtendedCanary.lean', ROOT / 'Tests/OnlineBregmanProximalCanary.lean', ROOT / 'BanditRLProof/OnlineSubgradientAbsolute.lean'])
write(RUN / 'BODY-canary-contract-review-inputs-v1.json', dict(rows=rows(paths),
    production_sha256=sha(PUBLIC), canary_body_absent=True, baseline_count=2955,
    whole_Goal_status='ACTIVE'))
fixed()
print('Eight actual BODYs and four exact concrete Test contracts ready for source review; no Test body.')
