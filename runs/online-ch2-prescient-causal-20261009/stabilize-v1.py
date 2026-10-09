from common import *
fixed()
assert not PUBLIC.exists()
review = RUN / 'contract-review-v1.json'
r = load(review)
assert r['verdict'] in ['accepted', 'accepted-with-explicit-delta'] and not r['required_repairs']
for row in load(RUN / 'contract-review-inputs-v1.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
d = load(CONTRACT / 'targets-draft-v1.json')
assert len(d['targets']) == 8 and len(d['definitions']) == 2
mutable = [RUN / n for n in ['lifecycle-sessions.jsonl', 'lifecycle-state.json', 'own-artifact-journal.md']]
mutable += [ROOT / x / (TASK + '.md') for x in ['tasks', 'proof-obligations', 'conversion-windows']]
write(RUN / 'pre-stabilization-exact-own-metadata-v1.json', dict(rows=[dict(path=p.as_posix(), sha256=sha(p), raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in mutable]))
write(CONTRACT / 'stabilized-v1.json', dict(stage='stabilized', targets=d['targets'], definitions=d['definitions'], semantic_slots=d['semantic_slots'], source_to_Lean_delta=d['source_to_Lean_delta'], dependency_DAG=d['dependency_DAG'], context_sha256=d['context_sha256'], source_card_sha256=d['source_card_sha256'], draft_sha256=sha(CONTRACT / 'targets-draft-v1.json'), review_sha256=sha(review), initial_lower_leaves=d['targets'][:1], local_proof_obligations=8, new_definitions=2, allowed_file=PUBLIC.as_posix(), edit_boundary='Only exact8frozen theorem bodies, two exact definition bodies when dependency selected, and necessary imports/context in new module. First selection locality only; no extra named helpers/oldroot/Test/readers/globalSGB. Semantic header/context/definition changes need newversion/review.', source_container_closed=False, chapter_proof_total=None, chapter_complete=False, whole_Goal_status='ACTIVE'))
suffix = '\nSource/CONTRACT accepted at ' + sha(review) + '. Eight exact headers/contexts and two exact partial-definition bodies frozen; proving starts with divergence_extension_eq only. Other7proofs/two definitions not yet materialized. Same-run fixed-variable/source interior transport/fullsource/all8forwards remain REQUIREDOPEN; chapterdenominatornull/wholeGoalACTIVE.\n'
for p in mutable[3:]:
    p.write_bytes(p.read_bytes() + suffix.encode('utf8'))
pins = [dict(declaration=t['declaration'], statement_hash=t['statement_hash']) for t in d['targets']]
event('stabilized-native-v1', 'stabilized', dict(contract_sha256=sha(CONTRACT / 'stabilized-v1.json'), review_sha256=sha(review), targets=pins, definitions=d['definitions'], source_container_closed=False, chapter_complete=False, goal_complete=False))
event('proving-native-v1', 'proving', dict(selected_leaves=pins[:1], allowed_file=PUBLIC.as_posix(), local_obligations=8, definitions_not_yet_materialized=True, source_container_closed=False, chapter_complete=False, goal_complete=False))
capture('leaf-running-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'running', '--attempt-id', 'PC001-extension-locality-v1', '--run-id', RUN.name, '--lean', PUBLIC.relative_to(ROOT).as_posix(), '--statement-hash', pins[0]['statement_hash'], '--obligations-before', '1', '--obligations-after', '1', '--notes', 'Only first dependency-ready frozen locality leaf selected; remaining7proofs/two exact definitions and fullsource fixed-variable/source interior obligations pending. No source/chapter closure.')
write(RUN / '30_lower-plan-v1.md', 'First frozen leaf only: X neighborhood of interior base implies eventual equality of ambient representatives; actual mathlib fderiv congruence plus equal source values gives same canonical ordered divergence. No regularity at boundary/default derivative licenses, no psi positivity/strictness inferred. No extra public wrappers; other7proofs/two definitions wait readiness selection. Focused build/public full VALUE/axioms/frozen fence required; canaries/BODY/combined/reader/site/FINAL/native/delivery separate. WholeGoalACTIVE.')
fixed()
print('Exact8proofs/2definitions stabilized; first locality leaf selected only.')
