from publication_guard_v2 import *
fixed()
old = load(CONTRACT / 'exact-publication-plan-v4.json')
assert len(old['rows']) == 6 and old['allowed_old_mutations'] == 5
new = json.loads(json.dumps(old))
new['allowed_old_mutations'] = 6
assert {k:v for k,v in new.items() if k != 'allowed_old_mutations'} == {k:v for k,v in old.items() if k != 'allowed_old_mutations'}
write(CONTRACT / 'exact-publication-plan-v5.json', new)
write(RUN / 'catalogue-count-repair-v5.json', dict(original_plan_sha256=sha(CONTRACT / 'exact-publication-plan-v4.json'),
    revised_plan_sha256=sha(CONTRACT / 'exact-publication-plan-v5.json'),
    exact_only_field='allowed_old_mutations', before=5, after=6,
    reason='Distinct reviewer caught stale inherited five-path count in prospective six-row plan; no canonical write or gate/acceptance performed.',
    rows_all_identical=True, production_Test_reader_and_generator_unchanged=True, whole_Goal_status='ACTIVE'))
s = (RUN / 'publication_guard_v3.py').read_text(encoding='utf8')
s = s.replace('catalogue-repair-binding-v4.json', 'catalogue-repair-binding-v5.json').replace('catalogue-repair-review-v4.json', 'catalogue-repair-review-v5.json').replace('exact-publication-plan-v4.json', 'exact-publication-plan-v5.json')
s = s.replace("    allowed = {row['path']: row for row in load(plan)['rows']}", "    assert load(plan)['allowed_old_mutations'] == len(load(plan)['rows']) == 6\n    allowed = {row['path']: row for row in load(plan)['rows']}")
write(RUN / 'publication_guard_v4.py', s)
for src, dst in [('prepare-stage-v3.py', 'prepare-stage-v4.py'),
                 ('run-combined-gates-v2.py', 'run-combined-gates-v3.py'),
                 ('commit-and-build-site-v3.py', 'commit-and-build-site-v4.py'),
                 ('verify-registry-v3.py', 'verify-registry-v4.py'),
                 ('run-file-browser-capture-v4.py', 'run-file-browser-capture-v5.py'),
                 ('prepare-FINAL-v5.py', 'prepare-FINAL-v6.py')]:
    s = (RUN / src).read_text(encoding='utf8').replace('publication_guard_v3', 'publication_guard_v4')
    s = s.replace('exact-publication-plan-v4.json', 'exact-publication-plan-v5.json')
    s = s.replace('verify-registry-v3.py', 'verify-registry-v4.py')
    for n in ['candidate-stage-plan', 'candidate-stage', 'candidate-full-diff-check', 'exact-RAW-line-ending-snapshots', 'candidate-diff-audit']:
        s = s.replace(n + '-v3', n + '-v4')
    s = s.replace("'catalogue-repair-review-v4.json']:", "'catalogue-repair-review-v4.json', 'catalogue-repair-review-v5.json']:")
    s = s.replace('Exact plan-v4 appends', 'Exact count-corrected plan-v5 appends')
    write(RUN / dst, s)
fixed()
print('Versioned exact one-field count correction; previous plan/helpers retained, no canonical write.')
