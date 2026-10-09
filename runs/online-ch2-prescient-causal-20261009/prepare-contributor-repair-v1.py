from publication_guard_v4 import *
fixed()
copied = []
for name, dst in [('candidate-commit-v3', 'catalogue-candidate-commit-v3'), ('contributor-stack-v3', 'catalogue-contributor-stack-failed-v3')]:
    p = ROOT / 'tmp' / (TASK + '-' + name + '.json')
    q = RUN / (dst + '.json')
    write(q, p.read_bytes())
    copied.append(dict(path=p.as_posix(), durable=q.as_posix(), sha256=sha(p)))
assert load(RUN / 'catalogue-candidate-commit-v3.json')['actual_exit'] == 0
assert load(RUN / 'catalogue-contributor-stack-failed-v3.json')['actual_exit'] == 1
old = load(CONTRIBUTION)
new = json.loads(json.dumps(old))
extra = 'website/content/declaration-boundaries.json'
assert extra not in old['affected_files']
new['affected_files'].append(extra)
assert {k:v for k,v in old.items() if k != 'affected_files'} == {k:v for k,v in new.items() if k != 'affected_files'}
write(RUN / 'contribution-before-range-ownership-v1.json', CONTRIBUTION.read_bytes())
write(RUN / 'contribution-after-range-ownership-v1.json', new)
write(RUN / 'contributor-failure-inspected-v3.json', dict(
    actual_clean_candidate_commit=subprocess.check_output(['git','rev-parse','HEAD'], encoding='utf8').strip(),
    actual_commit_exit=0, actual_contributor_stack_exit=1, failure='New declaration-boundaries production path missing from own affected_files manifest.',
    exact_proposed_only_field='affected_files append one config path', copied_receipts=copied,
    SITEv3_not_built=not SITE.exists(), production_Test_generator_unchanged=True,
    fresh_combined_full_passed=True, full_harness_sha256=sha(RUN / 'full-harness-inspected-v2.json'),
    native_accepted=False, FINAL_started=False, whole_Goal_status='ACTIVE'))
write(RUN / 'contributor-repair-packet-v1.md', '''# Exact own manifest range-ownership correction

Fresh combined/root/Tests/fullharness v2 passed with unchanged Lean and reviewed declaration-boundaries config. Clean candidate ff9bc7b79d2217415d2a68bdb9e7771f3f1e6c10 committed, but actual nonempty contributor-stack-v3 exited1: declaration-boundaries.json production path missing from OWN affected_files. Site did not start. Exact failed tmp receipts durably copied; no FINAL/accepted/package/chapter claim.

Review prospective contribution-after-range-ownership-v1.json: ONLY append website/content/declaration-boundaries.json to own affected_files, preserving every old entry and every other field. Six reviewed original oldpaths/plan-v5/config/frozen proof/Test/generator unchanged. This is attribution metadata, no target/schema/tool rule weakening. Existing fullharness applies to identical Lean/root/Test/pins/config; no claim it checked this contributor-base obligation or reran after manifest correction. Actual fresh two contributor bases and clean site/browser/22pixels/FINAL still required.

Run publication_guard_v4.fixed and independently rehash this bounded input manifest before/after, old vs new exact scalar/list diff and prior review plan bindings. Create-only contributor-repair-review-v1.md/json: verdict, materialization_verdict, required_repairs, report/report_sha256, input_manifest_sha256, approved_after_sha256, exact_affected_files_delta_only, raw_input_checks. Do not materialize/publicize. Other source/cumulative/all8forwards remain OPEN/GoalACTIVE; distinct reused staged requestedAstra-medium actor/history limits.
''')
paths = [PUBLIC, CANARY, CONTRIBUTION, ROOT/'website/content/declaration-boundaries.json', ROOT/'tools/check_contributor_contract.py',
    CONTRACT/'exact-publication-plan-v5.json', RUN/'catalogue-repair-binding-v5.json', RUN/'catalogue-repair-review-v5.json',
    RUN/'publication_guard_v4.py', RUN/'full-harness-inspected-v2.json', RUN/'combined-root-Tests-inspected-v2.json',
    RUN/'catalogue-candidate-commit-v3.json', RUN/'catalogue-contributor-stack-failed-v3.json',
    RUN/'contributor-failure-inspected-v3.json', RUN/'contributor-repair-packet-v1.md',
    RUN/'contribution-before-range-ownership-v1.json', RUN/'contribution-after-range-ownership-v1.json']
write(RUN/'contributor-repair-inputs-v1.json', dict(rows=rows(paths), exact_only_manifest_affected_files_append=True,
    canonical_manifest_unchanged=True, whole_Goal_status='ACTIVE'))
fixed()
print('Actual contributor gate failure retained; exact one-field ownership repair ready.')
