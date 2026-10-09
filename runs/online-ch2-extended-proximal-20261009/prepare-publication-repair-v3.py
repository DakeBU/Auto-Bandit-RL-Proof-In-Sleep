from common import *
import copy
fixed()
rp = RUN / 'canary-BODY-publication-review-v2.json'
assert sha(rp) == 'bb57516720327c62e067e4d8380baa46b32892f9d39d7dc15401de8bca29c2fc'
r = load(rp)
assert r['BODY_verdict'] == 'accepted-with-explicit-delta' and r['materialization_verdict'] == 'rejected'
for row in load(RUN / 'canary-BODY-publication-review-inputs-v2.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
a = 'has boundary minimizer p=0 at center −1 with objective minimum value 1/2, which is outside both V and the loss domain.'
b = 'has boundary minimizer p=0 and objective minimum value 1/2 when its center is −1. The center −1 is outside both V and the loss domain.'
proposal = copy.deepcopy(load(RUN / 'reader-proposal-v2.json'))
for note in proposal['notes']:
    assert note['lean_notes'].count(a) == 1
    note['lean_notes'] = note['lean_notes'].replace(a, b)
write(RUN / 'reader-proposal-v3.json', proposal)
plan = copy.deepcopy(load(CONTRACT / 'exact-publication-plan-v2.json'))
row = next(x for x in plan['rows'] if x['path'].endswith('/highlights.json'))
material = load(row['after_snapshot'])
byname = {n['full_name']: n for n in proposal['notes']}
material['highlights'] = [byname.get(n['full_name'], n) for n in material['highlights']]
dest = RUN / 'publication-after-highlights-v3.json'
write(dest, material)
row['after_snapshot'] = dest.as_posix()
row['after_sha256'] = sha(dest)
row['delta'] += ' Version3 explicitly makes center−1 the subject of the outside-domain sentence.'
plan['previous_plan_sha256'] = sha(CONTRACT / 'exact-publication-plan-v2.json')
plan['rejected_review_sha256'] = sha(rp)
plan['reader_proposal_sha256'] = sha(RUN / 'reader-proposal-v3.json')
write(CONTRACT / 'exact-publication-plan-v3.json', plan)
director = (RUN / 'publication-director-v2.md').read_text(encoding='utf8')
assert director.count(a) == 1
write(RUN / 'publication-director-v3.md', director.replace(a, b))
write(RUN / 'reader-wording-repair-v3.json', dict(
    rejected_review_sha256=sha(rp),
    reason='Corrected objective value1/2 must not become antecedent of outside-domain statement.',
    exact_old_sentence=a, exact_new_sentence=b,
    new_note_fields_changed=3, director_changed=True, legacy_eight_fields_unchanged_from_v2=True,
    production_Test_and_frozen_headers_unchanged=True, no_actual_materialization=True,
    after_plan_sha256=sha(CONTRACT / 'exact-publication-plan-v3.json'),
    package_accepted=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
write(RUN / 'canary-BODY-publication-review-packet-v3.md', '''# Version3: explicit outside center, same frozen mathematics

Rehash all RAW and2925baseline before/after; common.fixed. v2 BODY remains accepted-with-explicit-delta; materialization rejected solely for the new sentence antecedent. Its R9 objective numbers and L1 eight legacy fields were accepted, preserved byte-for-byte from v2. Production/Test/frozen headers/actual compiled VALUE/axiom/safe/numeric-tail/graph evidence unchanged. No mathematical recompile is claimed after only prospective reader edits.

Review exact-publication-plan-v3.json, reader-proposal-v3.json, director-v3 and reader-wording-repair-v3.json. ONLY three new lean_notes fields and the prospective director replace the one sentence with: has boundary minimizer p=0 and objective minimum value1/2 when its center is−1. The center−1 is outside both V and the loss domain. Actual exact sentence with spaces is bound in repairJSON. Root/Testroot/chapter/reading v2 snapshots and all eight explicit legacy corrections remain unchanged. Five prospective old paths only; no actual old bytes changed. Independently confirm AST deltas, R1–R8/R9/L1 all satisfied, existing IDs/formulas/links/dependencies/otherBooks and unrelated T0 text preserved.

Create-only canary-BODY-publication-review-v3.md/json, one final LF/no trailing whitespace. Separate BODY_verdict/materialization_verdict, required_repairs and approved_five_rows/planSHA/production Test/input/report SHAs. Only exact five-path materialization may be authorized. Combined gates/registry/site/DOM/pixels/FINAL/native/postnative/delivery still pending; whole16GoalACTIVE/all8forwards/general source X/interior/extension locality/current attained causal recursion/interiority/fixed-variable same-run sharp telescopes OPEN. Requested Astra/medium reused staged distinct automated role; no human/external/absolute-blind/runtime attestation. Actual baseline full checks mandatory, count/digest receipt sufficient; do not edit original inputs.
''')
excluded = {'lifecycle-state.json', 'lifecycle-sessions.jsonl', 'own-artifact-journal.md', 'trials.jsonl'}
paths = [PUBLIC, ROOT / 'Tests/OnlineBregmanExtendedCanary.lean'] + [x for x in RUN.iterdir() if x.is_file() and x.name not in excluded] + list(CONTRACT.glob('*'))
write(RUN / 'canary-BODY-publication-review-inputs-v3.json', dict(rows=rows(paths),
    baseline_count=2925, exact_plan_sha256=sha(CONTRACT / 'exact-publication-plan-v3.json'),
    prior_rejected_review_sha256=sha(rp), no_existing_input_changes=True, no_actual_materialization=True,
    package_accepted=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
event('reader-repair-native-v3', 'repair', dict(rejected_review_sha256=sha(rp),
    versioned_repair_sha256=sha(RUN / 'reader-wording-repair-v3.json'), target_revision=False,
    scope='Only prospective sentence antecedent clarified; no materialization; distinct re-review pending.',
    source_container_closed=False, chapter_complete=False, goal_complete=False))
fixed()
print('Version3 explicit outside-center sentence ready for exact re-review; all previous versions retained.')
