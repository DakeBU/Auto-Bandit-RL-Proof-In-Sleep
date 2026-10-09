from publication_guard_v2 import *
fixed()
r = load(RUN / 'catalogue-repair-review-v4.json')
assert r['required_repairs'] and sha(r['report']) == r['report_sha256']
assert load(CONTRACT / 'exact-publication-plan-v5.json')['allowed_old_mutations'] == 6
write(RUN / 'catalogue-repair-review-packet-v5.md', '''# Versioned prospective catalogue repair count correction

Continue distinct anti-anchored source review. Read original catalogue-repair-review-packet-v4/inputs-v4 and your immutable rejected materialization review-v4. Actual failure/source-range evidence remains unchanged. Exact plan-v5 differs from v4 ONLY allowed_old_mutations5->6, now matching its exact six rows. catalogue-count-repair-v5.json binds both plans. No canonical write or fresh gate/pixel/FINAL/acceptance occurred. Existing boundary tests and independent complete scan only iterate delta are historical applicable evidence, not newly rerun claims.

Run publication_guard_v2.fixed, independently rehash before/after new inputs. Verify full existing FTL entry preserved and new range33-36 equals entire previously frozen iterate definition, RAW source/full LF block hashes exact. Five original final plan rows unchanged. Exact sixth config mutation is one appended source-qualified range using existing generator support; no generator/Lean/Test/contract mathematical change. All full-source/valid generated interior run/sharp fixed/variable obligations remain REQUIRED/OPEN and GoalACTIVE.

Create-only catalogue-repair-review-v5.md/json with verdict/materialization_verdict/required_repairs/report/report_sha256/input_manifest_sha256/approved_plan_sha256/approved_six_rows/raw_input_checks/exact_boundary_delta_only; explicitly resolve M1 without overwriting original review. Acceptance is permission for exact prospective materialization only, followed by fresh combined/site/registry/browser/22originals and distinct FINAL. No human/external/absolute-blind/runtime attestation; staged related history disclosed.
''')
paths = {p for d in [RUN, CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([PUBLIC, CANARY, CONTRIBUTION, PDF, ROOT / 'website/content/declaration-boundaries.json', ROOT / 'website/scripts/build_site.py', ROOT / 'tools/test_source_declaration_boundaries.py'])
write(RUN / 'catalogue-repair-review-inputs-v5.json', dict(rows=rows(paths), previous_required_repair='M1 stale allowed_old_mutations count',
    exact_v4_to_v5_only_count_field=True, whole_Goal_status='ACTIVE'))
fixed()
print('New count-corrected review packet ready; original rejection preserved.')
