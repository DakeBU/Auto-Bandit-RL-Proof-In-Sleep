from publication_guard_v2 import *
from website.scripts import build_site as site
from unittest.mock import patch
fixed()
path = ROOT / 'website/content/declaration-boundaries.json'
before = path.read_bytes()
old = load(path)
source = PUBLIC.read_text(encoding='utf8').splitlines()
start = next(i + 1 for i, line in enumerate(source) if line.startswith('def iterate '))
end = start + 3
block = '\n'.join(source[start - 1:end])
definition = next(d for d in load(CONTRACT / 'stabilized-v1.json')['definitions'] if d['declaration'].endswith('.iterate'))
assert block == definition['exact_definition']
entry = dict(full_name='BanditRL.OnlinePrescientBregman.iterate',
    file=PUBLIC.relative_to(ROOT).as_posix(), file_sha256=sha(PUBLIC), start_line=start, end_line=end,
    block_LF_sha256=hashlib.sha256(block.encode('utf8')).hexdigest(),
    reason='Reviewed complete frozen equation-style definition; source-qualified RAW file and full LF block pins exclude the next theorem without changing Lean.')
assert not any(x['full_name'] == entry['full_name'] for x in old['entries'])
after = json.loads(json.dumps(old))
after['entries'].append(entry)
old_modules = site.scan_lean_tree()
with patch.object(site, 'load_declaration_boundaries', return_value=after['entries']):
    new_modules = site.scan_lean_tree()
diffs = []
assert len(old_modules) == len(new_modules)
for a, b in zip(old_modules, new_modules):
    assert {k:v for k,v in a.items() if k != 'declarations'} == {k:v for k,v in b.items() if k != 'declarations'}
    assert len(a['declarations']) == len(b['declarations'])
    for x, y in zip(a['declarations'], b['declarations']):
        if x != y:
            assert {k:v for k,v in x.items() if k != 'statement'} == {k:v for k,v in y.items() if k != 'statement'}
            diffs.append(dict(full_name=x['full_name'], before=x['statement'], after=y['statement']))
assert len(diffs) == 1 and diffs[0]['full_name'] == entry['full_name']
assert 'theorem advance_some_spec' in diffs[0]['before']
assert diffs[0]['after'] == ' '.join(line.strip() for line in source[start - 1:end])
write(RUN / 'publication-before-declaration-boundaries-v4.json', before)
write(RUN / 'publication-after-declaration-boundaries-v4.json', after)
plan = load(CONTRACT / 'exact-publication-plan-v3.json')
baseline = next(r for r in load(RUN / 'baseline-v1.json')['rows'] if r['path'] == path.as_posix())
assert baseline['sha256'] == sha(path)
plan['rows'].append(dict(path=path.as_posix(), before_sha256=sha(path),
    before_snapshot=(RUN / 'publication-before-declaration-boundaries-v4.json').as_posix(),
    after_snapshot=(RUN / 'publication-after-declaration-boundaries-v4.json').as_posix(),
    after_sha256=sha(RUN / 'publication-after-declaration-boundaries-v4.json'),
    delta='Append exactly one reviewed full frozen iterate definition range to existing schema1; preserve original FTL entry and every other old field.'))
plan['prospective_refinement'] = 'Original five final rows unchanged. Sixth old file appends one exact source-qualified definition boundary; existing generator implementation and frozen Lean remain unchanged.'
write(CONTRACT / 'exact-publication-plan-v4.json', plan)
write(RUN / 'catalogue-failure-inspected-v3.json', dict(status='REPAIR',
    actual_browser_exit=0, source_commit=load(RUN / 'clean-candidate-site-binding-v2.json')['actual_head'],
    root_personally_viewed_originals=rows(RUN / n for n in load(RUN / 'formula-render-v3-browser.json')['images']),
    image_count=22, observed_image='module-declaration-10-v3.png',
    failure='Equation-style iterate catalogue statement includes the following advance_some_spec theorem header. Successful browser/geometry and registry identity preservation did not establish correct source range.',
    proposed_entry=entry, actual_in_memory_complete_scan_differences=diffs,
    every_other_scanned_declaration_equal=True, old_config_preserved=True,
    production_Test_frozen_contracts_and_generator_unchanged=True, FINAL_started=False,
    native_accepted=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
capture('existing-source-boundary-tests-v4', sys.executable, '-B', '-X', 'utf8', '-m', 'unittest', 'tools.test_source_declaration_boundaries')
write(RUN / 'catalogue-repair-review-packet-v4.md', '''# Exact equation-definition catalogue range repair

Root personally viewed all22 original v3 screenshots from repaired SITEv2. Completion premise now renders, but iterate catalogue includes its entire equation-style definition PLUS next advance_some_spec theorem header. Preserve actual v3 DOM/pixels and failure inspection. No FINAL/accepted event occurred. This is an exact-source presentation failure, not a Lean target/proof failure.

Existing source-qualified declaration-boundaries.json schema1 already supports reviewed complete equation-style definitions. Do not modify generator/Lean. Proposed plan-v4 preserves all five approved final rows from plan-v3, and adds a sixth old path: append ONLY the iterate source range33-36 with RAW file SHA and exact LF whole-definition block SHA, preserving original FTL range entry/every old field. Its block equals the previously frozen whole definition. Existing6 meaningful boundary tests passed; actual complete in-memory production scan finds exactly this one statement changed, every other declaration and field equal. Source scope, assumptions, all8forwards/full-source/sharp cumulative bounds remain OPEN/GoalACTIVE.

Review prospective publication-after-declaration-boundaries-v4 and exact-publication-plan-v4 independently. Run publication_guard_v2.fixed and rehash all current input rows before/after. Only new config write may be materialized after approval. Fresh combined harness/site/check/shared registry and browser/pixels/FINAL required afterward; no fresh compiled or repaired pixel claim now. Preserve previous failures and review bindings. Distinct staged automated source reviewer, requested Astra/medium, related history disclosed; no human/external/absolute blind/runtime attestation.

Create-only catalogue-repair-review-v4.md/json, required fields verdict, materialization_verdict, required_repairs, report, report_sha256, input_manifest_sha256, approved_plan_sha256, approved_six_rows, raw_input_checks, exact_boundary_delta_only. All five prior transitions remain exactly bound; no semantic weakening or chapter/package acceptance.
''')
fixed()
paths = {p for d in [RUN, CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([path, PUBLIC, CANARY, CONTRIBUTION, PDF, ROOT / 'website/scripts/build_site.py', ROOT / 'tools/test_source_declaration_boundaries.py'])
write(RUN / 'catalogue-repair-review-inputs-v4.json', dict(rows=rows(paths), exact_one_new_boundary_entry=True,
    all_old_five_final_rows_preserved=True, whole_Goal_status='ACTIVE'))
print('Exact frozen-definition range repair ready for distinct review; no canonical write.')
