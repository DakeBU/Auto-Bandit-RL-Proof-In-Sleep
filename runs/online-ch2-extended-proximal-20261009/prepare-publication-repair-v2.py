from common import *
import copy
fixed()
rp = RUN / 'canary-BODY-publication-review-v1.json'
assert sha(rp) == '086b03bee33bc4a076022432e8e4d1167f1f390b539c79691d621ac5c4a49d19'
r = load(rp)
assert r['BODY_verdict'] == 'accepted-with-explicit-delta' and r['materialization_verdict'] == 'rejected'
assert {x['id'] for x in r['required_repairs']} == {'R9-wording', 'L1-legacy-wording'}
for row in load(RUN / 'canary-BODY-publication-review-inputs-v1.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
replacements = [
    ('has actual minimum 0 at center 1/2,', 'has minimizer p=0 at center 1/2 with objective minimum value 11/64,'),
    ('has actual boundary minimum 0 at center −1,', 'has boundary minimizer p=0 at center −1 with objective minimum value 1/2,')]
proposal = copy.deepcopy(load(RUN / 'reader-proposal-v1.json'))
for n in proposal['notes']:
    for a, b in replacements:
        assert n['lean_notes'].count(a) == 1
        n['lean_notes'] = n['lean_notes'].replace(a, b)
legacy_replacements = [
    ('center1/2 and minimum0;', 'center1/2 and minimizer p=0 (objective minimum value11/64);'),
    ('center-1 outsideV and boundary minimum0.', 'center-1 outsideV and boundary minimizer p=0 (objective minimum value1/2).')]
plan = copy.deepcopy(load(CONTRACT / 'exact-publication-plan-v1.json'))
legacy = []
prior_contract = load(ROOT / 'docs/contracts/online-ch2-bregman-v1/stabilized-v1.json')
prior_names = {prior_contract['definition']['declaration']} | {t['declaration'] for t in prior_contract['targets']}
assert len(prior_names) == 6
for n in ['readings', 'highlights']:
    row = next(x for x in plan['rows'] if x['path'].endswith('/' + n + '.json'))
    material = load(row['after_snapshot'])
    if n == 'highlights':
        byname = {x['full_name']: x for x in proposal['notes']}
        material['highlights'] = [byname.get(x['full_name'], x) for x in material['highlights']]
        targets = [(x, 'lean_notes', 'highlights/' + x['full_name'] + '/lean_notes')
            for x in material['highlights'] if x['full_name'] in prior_names]
        assert len(targets) == 6
    else:
        reading = next(x for x in material['readings'] if x['slug'] == proposal['route'])
        cards = [x for x in reading['source_theorems'] if x['label'] == 'Chapter2 prescient dependency: canonical Bregman algebra and real proximal step']
        assert len(cards) == 1
        card = cards[0]
        targets = [(card, 'plain', 'readings/online-ogd/source_theorems/legacy-Bregman/plain'),
            (card['contract'], 'guarantee', 'readings/online-ogd/source_theorems/legacy-Bregman/contract/guarantee')]
    for obj, field, path in targets:
        before = obj[field]
        after = before
        for a, b in legacy_replacements:
            assert after.count(a) == 1, path
            after = after.replace(a, b)
        obj[field] = after
        legacy.append(dict(field_path=path, before=before, after=after,
            before_utf8_sha256=hashlib.sha256(before.encode('utf8')).hexdigest(),
            after_utf8_sha256=hashlib.sha256(after.encode('utf8')).hexdigest(),
            reason='Clarify minimizer point versus minimum objective value; no proof/contract/ID/formula/link change.'))
    dest = RUN / ('publication-after-' + n + '-v2.json')
    write(dest, material)
    row['after_snapshot'] = dest.as_posix()
    row['after_sha256'] = sha(dest)
    row['delta'] += ' Explicit versioned minimum/minimizer wording corrections: ' + ('six legacy note fields and three new note fields.' if n == 'highlights' else 'two fields of the legacy Bregman source card.')
assert len(legacy) == 8
proposal['legacy_reader_wording_corrections'] = legacy
write(RUN / 'reader-proposal-v2.json', proposal)
plan['previous_plan_sha256'] = sha(CONTRACT / 'exact-publication-plan-v1.json')
plan['rejected_review_sha256'] = sha(rp)
plan['reader_proposal_sha256'] = sha(RUN / 'reader-proposal-v2.json')
plan['legacy_reader_wording_corrections'] = legacy
plan['other_old_fields_immutable'] = True
write(CONTRACT / 'exact-publication-plan-v2.json', plan)
director = (RUN / 'publication-director-v1.md').read_text(encoding='utf8')
for a, b in replacements:
    assert director.count(a) == 1
    director = director.replace(a, b)
director += '\nVersioned repair R9/L1: the same five file paths now explicitly include eight legacy wording fields (six notes and two fields of one card), with exact before/after strings. All other legacy fields, mathematical declarations, frozen contracts, receipts, IDs, formulas, links and unrelated T0 wording remain fixed. Prior v1 is retained and was never applied.\n'
write(RUN / 'publication-director-v2.md', director)
write(RUN / 'reader-wording-repair-v2.json', dict(
    rejected_review_sha256=sha(rp), required_repairs=['R9-wording', 'L1-legacy-wording'],
    before_plan_sha256=sha(CONTRACT / 'exact-publication-plan-v1.json'),
    after_plan_sha256=sha(CONTRACT / 'exact-publication-plan-v2.json'),
    new_note_fields_corrected=3, legacy_note_fields_corrected=6, legacy_card_fields_corrected=2,
    mathematical_basis='At minimizer p=0 each loss is zero; the objective equals its movement divergence, proved as11/64 and1/2 by the exact prior/current canaries.',
    production_Test_and_frozen_headers_unchanged=True, no_actual_materialization=True,
    package_accepted=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
write(RUN / 'canary-BODY-publication-review-packet-v2.md', '''# Versioned exact reader repair, BODY unchanged

Rehash all RAW and 2925 baseline before/after; common.fixed. Prior v1 BODY accepted-with-explicit-delta, materialization REJECTED for R9/L1. All185 original input rows remain unchanged. Current production/Test/frozen headers/actual compiled VALUEs/standard axioms/true selected Eq.mp numeric tails and generated Test auxiliary are identical to v1 accepted BODY. No proof repair since then.

Review exact-publication-plan-v2.json and reader-proposal-v2.json/publication-director-v2.md. New three note fields now explicitly say minimizer p=0, with actual objective minimum values11/64 and1/2. Same FIVE old file paths only: root/Testroot imports and chapter suffix are exactly v1 prospective bytes, still unapplied. Highlights now explicitly correct six legacy Bregman lean_notes fields; readings explicitly correct plain and contract.guarantee of the one existing Bregman source card. Complete eight exact old/new strings and UTF8 hashes are bound in the new plan. These legacy updates are the explicit L1 scope extension, not a claim that v1 preserved-and-fixed them. Other fields/IDs/formulas/dependencies/links and all other Books are fixed; unrelated T0 empty-minimum0 text is fixed. Original proof/contracts/receipts remain immutable. No new Lean result or source erratum.

Independently compare after snapshots at AST field level to old current bytes and v1 snapshots: only specified appends and R9/L1 wording fields, no hidden change. Resolve all R1–R8 as well. Separately return BODY_verdict and materialization_verdict plus exact approved_five_rows/plan SHA and required_repairs. Only exact five-path materialization may be authorized; no native acceptance, full source/chapter/Goal completion or publication. Combined root/Tests/full harness/shared registry/site/DOM/original pixels/FINAL/native/postnative/delivery remain pending. Whole Goal ACTIVE; all eight forwards and source X/interior/extension locality/current-loss attained causal recursion/interiority/sharp fixed-variable same-run telescopes remain REQUIRED/OPEN.

Create-only canary-BODY-publication-review-v2.md/json, one final LF/no trailing whitespace. Requested Astra/medium reused staged distinct automated role, no human/external/absolute-blind/runtime attestation. Verify every baseline but store count/digest rather than repeat all2925rows. Do not edit existing input files.
''')
excluded = {'lifecycle-state.json', 'lifecycle-sessions.jsonl', 'own-artifact-journal.md', 'trials.jsonl'}
paths = [PUBLIC, ROOT / 'Tests/OnlineBregmanExtendedCanary.lean'] + [x for x in RUN.iterdir() if x.is_file() and x.name not in excluded] + list(CONTRACT.glob('*'))
write(RUN / 'canary-BODY-publication-review-inputs-v2.json', dict(rows=rows(paths),
    baseline_count=2925, exact_plan_sha256=sha(CONTRACT / 'exact-publication-plan-v2.json'),
    prior_rejected_review_sha256=sha(rp), no_existing_input_changes=True, no_actual_materialization=True,
    package_accepted=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
print('R9/L1 versioned reader repair with eight explicit legacy fields and same five prospective paths ready for re-review.')
