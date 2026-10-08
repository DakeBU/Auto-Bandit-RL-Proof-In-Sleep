from common_v1 import *

fixed()
assert load(RUN / 'draft-type-verification-v1.json')['actual_identity_gate'] == 'actual-draft-neutral-identities-universe-v2'
blind = load(RUN / 'blind-receipt-v1.json')
assert blind['actor']['task'] == '/root/osd_blind' and not blind['ambiguities']
assert sha(blind['report']['path']) == blind['report']['sha256_raw_bytes']
before = '(hpb : ∀ t z, policy t z ∈ Set.Icc (0 : ℝ) 1)'
after = '(hpb : ∀ t z, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) →\n      policy t z ∈ Set.Icc (0 : ℝ) 1)'
targets = load(CONTRACT / 'targets-v1.json')
old_targets_sha = sha(CONTRACT / 'targets-v1.json')
changed = []
for row in targets['rows']:
    if before in row['header']:
        assert row['id'] in ['I005', 'I008'] and row['header'].count(before) == 1
        row['prior_v1_header_sha256'] = row['header_sha256']
        row['header'] = row['header'].replace(before, after)
        row['header_sha256'] = hashlib.sha256(row['header'].encode('utf8')).hexdigest()
        changed.append(row['id'])
assert changed == ['I005', 'I008']
targets['version'] = 2
targets['prior_v1_targets_sha256'] = old_targets_sha
targets['revision'] = 'Policy feasibility is required only on unit-interval strict-history tuples, matching legal source inputs; same conclusion, weaker unnecessary input hypothesis.'
write(CONTRACT / 'targets-v2.json', targets)
neutral_v1 = (CONTRACT / 'neutral-context-v1.lean').read_text(encoding='utf8')
draft_v1 = (RUN / 'draft-types-and-API-v1.lean').read_text(encoding='utf8')
assert neutral_v1.count(before) == draft_v1.count(before) == 2
write(CONTRACT / 'neutral-context-v2.lean', neutral_v1.replace(before, after))
write(RUN / 'draft-types-and-API-v2.lean', draft_v1.replace(before, after))
packet_v1 = (RUN / 'neutral-packet-v1.md').read_text(encoding='utf8')
assert packet_v1.count(before) == 2
write(RUN / 'neutral-packet-v2.md', packet_v1.replace(before, after))
write(RUN / 'neutral-inputs-v2.json', dict(rows=[dict(path=p.resolve().as_posix(), sha256=sha(p)) for p in
    [RUN / 'neutral-packet-v2.md', CONTRACT / 'neutral-context-v2.lean']], terminal_count=8, definition_count=4,
    prior_v1_input_manifest_sha256=sha(RUN / 'neutral-inputs-v1.json')))
contract_v1 = (CONTRACT / 'contract-v1.md').read_text(encoding='utf8')
contract_v2 = contract_v1.replace('# Version1 draft:', '# Version2 draft:', 1)
contract_v2 = contract_v2.replace('targets-v1/public-context-v1', 'targets-v2/public-context-v1')
contract_v2 = contract_v2.replace('are measurable and bounded for all tuples', 'are measurable and bounded on all LEGAL unit-interval tuples')
contract_v2 += '\n\nDraft v1 remains exact and is not stabilized/accepted. Formalizer source-hypothesis audit removes the unnecessary globally bounded real-history assumption in ONLY I005/I008: '
contract_v2 += 'policy outputs must be feasible whenever every strict-history coordinate is in[0,1]. Actual observed histories satisfy this a.s.; derive prediction L2 using ae_all_iff and this legal-input premise. '
contract_v2 += 'All six other headers, both complete benchmark definitions, source PDF/pages and conclusions stay exact. This strengthens coverage, rather than weakening a proof terminal. '
contract_v2 += 'A new distinct reconstruction/source review and explicit version2 stabilization are required before proving; v1 reconstruction does not certify v2.\n'
write(CONTRACT / 'contract-v2.md', contract_v2)
requirements = load(CONTRACT / 'reader-requirements-v1.json')
requirements[1]['requirement'] += ' Policy feasibility is required only on legal unit-interval strict-history tuples; actual history support and prediction L2 must be produced a.s.'
write(CONTRACT / 'reader-requirements-v2.json', requirements)
card = load(CONTRACT / 'source-card-v1.json')
card['version'] = 2
card['delta'].append('Only legal history tuples require feasible policy outputs; formalizer versioned hypothesis audit removed unnecessary all-real-tuples bound before proving.')
write(CONTRACT / 'source-card-v2.json', card)
fingerprint = load(CONTRACT / 'source-fingerprint-v1.json')
fingerprint['version'] = 2
fingerprint['targets_sha256'] = sha(CONTRACT / 'targets-v2.json')
fingerprint['source_card_sha256'] = sha(CONTRACT / 'source-card-v2.json')
fingerprint['prior_v1_source_fingerprint_sha256'] = sha(CONTRACT / 'source-fingerprint-v1.json')
write(CONTRACT / 'source-fingerprint-v2.json', fingerprint)
dag = load(CONTRACT / 'initial-DAG-v1.json')
dag['version'] = 2
dag['nodes'] = targets['rows']
dag['history_support_route'] = 'ae_all_iff(hb); observed tuple legal a.s.; hpb on legal inputs; MemLp_of_bounded; actual history_policy_independent.'
write(CONTRACT / 'initial-DAG-v2.json', dag)
obligations = load(RUN / 'proof-obligations-draft-v1.json')
obligations['version'] = 2
for row, target in zip(obligations['rows'], targets['rows']):
    assert row['id'] == target['id']
    row['frozen_header_sha256'] = target['header_sha256']
write(RUN / 'proof-obligations-draft-v2.json', obligations)
ledger = load(CONTRACT / 'chapter-one-source-ledger-draft-v1.json')
ledger['current_package_only'] = 'Current eight-target expected-fixed-minimum/LEGAL strict-history causal IID benchmark contractv2 DRAFT; original v1 and prior accepted packages preserved.'
ledger['current_contract_version'] = 2
write(CONTRACT / 'chapter-one-source-ledger-draft-v2.json', ledger)
write(RUN / 'contract-revision-v2.json', dict(status='draft audit revision; source review pending',
    changed_ids=changed, reason='Source algorithms need feasible outputs on legal pasts only, not arbitrary real tuples.',
    prior_v1_targets_sha256=old_targets_sha, targets_v2_sha256=sha(CONTRACT / 'targets-v2.json'),
    prior_v1_blind_receipt_sha256=sha(RUN / 'blind-receipt-v1.json'),
    six_other_raw_headers_unchanged=True, whole_definitions_source_PDF_unchanged=True, conclusions_unchanged=True,
    proof_bodies_not_started=True, chapter_complete=False, goal_complete=False))
for folder in ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints', 'research-wiki/retrieval-index']:
    p = Path(folder) / (TASK + '.md')
    p.write_bytes(p.read_bytes() + ('\n\n## Version2 draft source-hypothesis audit\n\n' +
        'Only I005/I008 policy-output premise now applies to LEGAL unit-interval histories; derive real observed history support a.s. before L2. '
        'Original v1 bytes/reconstruction and universe-check failure preserved. Eight conclusions, six other raw headers, definitions/source unchanged. '
        'No source acceptance/body yet; v2 needs its own reconstruction/reviewer. Target SHA ' + sha(CONTRACT / 'targets-v2.json') + '\n').encode('utf8'))
native('draft-contract-revision-v2', 'lifecycle-event', '--session', TASK, '--event', 'repair', '--payload-json', json.dumps(dict(
    phase='draft source-hypothesis audit', contract_version=2, prior_contract_version=1,
    revision=(RUN / 'contract-revision-v2.json').as_posix(), body_proofs_not_started=True,
    conclusion_unchanged=True, source_accepted=False, chapter_complete=False, goal_complete=False)))
gate('actual-draft-types-and-API-v2', 'lake', 'env', 'lean', RUN / 'draft-types-and-API-v2.lean')
gate('actual-neutral-types-v2', 'lake', 'env', 'lean', CONTRACT / 'neutral-context-v2.lean')
draft = (RUN / 'draft-types-and-API-v2.lean').read_text(encoding='utf8')
neutral = (CONTRACT / 'neutral-context-v2.lean').read_text(encoding='utf8')
identities = ['example : DraftExpected.Q' + str(i).zfill(3) + '.{u} = NeutralExpected.Q' + str(i).zfill(3) + '.{u} := rfl' for i in range(1,9)]
identities += ['example : @BanditRL.OnlineLearning.' + name + ' = @NeutralExpected.C' + str(i) + ' := rfl' for i, name in
    enumerate(['expectedFixedMinimum', 'expectedFixedRegret', 'empiricalMean', 'meanPredict'])]
write(RUN / 'draft-neutral-identities-v2.lean', 'import Mathlib\n' + draft + '\n' + neutral[len('import Mathlib\n'):] +
    '\nuniverse u\n' + '\n'.join(identities) + '\n')
gate('actual-draft-neutral-identities-v2', 'lake', 'env', 'lean', RUN / 'draft-neutral-identities-v2.lean')
write(RUN / 'draft-type-verification-v2.json', dict(status='passed', contract_version=2,
    eight_closed_Prop_type_identities=True, four_whole_definition_identities=True, arbitrary_shared_universe='u', actual_API_checks=True,
    targets_sha256=sha(CONTRACT / 'targets-v2.json'), public_context_sha256=sha(CONTRACT / 'public-context-v1.lean'),
    neutral_context_sha256=sha(CONTRACT / 'neutral-context-v2.lean'), new_public_proof_bodies_compiled=False,
    source_fidelity_accepted=False, chapter_complete=False, goal_complete=False))
fixed()
print('Version2 legal-history contract/types/identities compiled; distinct v2 reconstruction/source stabilization required.')
