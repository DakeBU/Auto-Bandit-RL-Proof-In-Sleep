from publication_guard_v1 import *
fixed()
p = load(RUN / 'reader-proposal-v2.json')
note = next(x for x in p['notes'] if x['full_name'] == 'BanditRL.OnlinePrescientBregman.iterate_complete_of_step_attained')
old = note['math']
new = old.replace(r'\begin{gathered}[', r'\begin{gathered}\bigl[').replace(r'F_{t,x}(z)]', r'F_{t,x}(z)\bigr]')
assert old != new and r'\begin{gathered}[' not in new
note['math'] = new
write(RUN / 'reader-proposal-v3.json', p)
highlights = load(ROOT / 'website/content/highlights.json')
target = next(x for x in highlights['highlights'] if x['full_name'] == note['full_name'])
assert target['math'] == old
target['math'] = new
write(RUN / 'publication-after-highlights-v3.json', highlights)
plan = load(CONTRACT / 'exact-publication-plan-v2.json')
row = next(x for x in plan['rows'] if x['path'] == (ROOT / 'website/content/highlights.json').as_posix())
row['after_snapshot'] = (RUN / 'publication-after-highlights-v3.json').as_posix()
row['after_sha256'] = sha(row['after_snapshot'])
row['delta'] = 'Preserve all old notes; ten new notes as reviewed, with completion display bracket protected from gathered optional-alignment parsing.'
plan['reader_proposal_sha256'] = sha(RUN / 'reader-proposal-v3.json')
plan['prospective_refinement'] = 'Exactly one new-note math field: bigl/bigr protect premise brackets from gathered optional alignment. No Lean, assumption, quantifier, conclusion or other reader field changes.'
write(CONTRACT / 'exact-publication-plan-v3.json', plan)
write(RUN / 'render-failure-inspected-v1.json', dict(
    status='REPAIR', actual_browser_command_exit=0, automatic_container_error_geometry_checks_passed=True,
    original_source_commit=load(RUN / 'clean-candidate-site-binding-v1.json')['actual_head'],
    viewed_originals=rows(RUN / n for n in load(RUN / 'formula-render-v1-browser.json')['images'][:12]),
    personally_viewed_original_count=12, observed_image='public-note-7-v1.png',
    actual_lost_premise=True, cause='The leading [ immediately after begin{gathered} is parsed as its optional alignment argument; MathJax silently emits only the final implication. Actual DOM assistive MathML mtable align attribute contains the missing premise.',
    old_math=old, proposed_math=new, exact_one_new_math_field_only=True,
    production_Test_and_frozen_contracts_unchanged=True, native_acceptance=False,
    FINAL_not_started=True, full_source_chapter_complete=False, whole_Goal_status='ACTIVE'))
write(RUN / 'render-inspection-tool-failures-v1.md',
    'Two read-only ad-hoc inspection commands failed before usable inspection: bs4 unavailable, then PowerShell inline quoting caused Python EOL SyntaxError. No dependency installed or source edited. The retained inspect-completion-render-v1.py uses stdlib exact strings and succeeded; its generated/actual DOM output identified gathered optional-alignment parsing. These are inspection-tool failures, not Lean proof failures.\n')
event('render-repair-native-v3', 'repair', dict(reason='Original pixel/actual DOM review found silently missing attainment premise in completion formula; no Lean target change.',
    evidence_sha256=sha(RUN / 'render-failure-inspected-v1.json'), allowed_scope='Prospective exact one-new-note math field only; distinct review required before materialization.',
    chapter_complete=False, goal_complete=False))
write(RUN / 'render-repair-review-packet-v3.md', '''# Exact rendering repair review

Read publication_guard_v1.fixed (2955 baseline with exactly original approved five transitions), current production/Test unchanged, original canary BODY/publication review-v1 and plan-v2, complete combined root9111/Tests9282/full472tests7existing skips/exporter/checkpassed, two nonempty contributor bases and actual clean SITEv1 commit1cf622876e815df8336788866d12747d0ecdf1cd. Registry11005unchanged+10new=11015 passed. Actual browser exit0/13sourcecontainers/zeroerrors/geometry passed, yet root personally viewed first12 originals and found note7 missing its entire attainment premise. Preserve all original failed render/DOM/pixels/receipts. No FINAL or native accepted event occurred.

Cause: begin{gathered} immediately followed by [ treats the bracketed premise as optional alignment. Actual DOM mtable align contains the entire missing premise and visible MathML only conclusion. The stdlib inspect helper succeeded after two recorded read-only ad-hoc tool failures (bs4 unavailable/inline quoting). This is a display failure, not a theorem/contract/proof failure.

Review prospective reader-proposal-v3 and exact-publication-plan-v3. Exactly one newly added highlight.math changes: begin{gathered}bigl[ and bigr] protect the same fully quantified bracketed premise. All original fields, old links, other Books, eight proof headers/bodies, two exact definitions and four canary headers/bodies remain fixed. Approve exact five final rows conditional on actual focused/combined fingerprints unchanged; only highlights requires a new canonical write, the other four after bytes already match. No generator or other old path change. Parent/source mathematical statements unchanged; all source X/interior/valid-run and sharp fixed/variable main-text endpoints/all8forwards remain OPEN/wholeGoalACTIVE.

Create-only render-repair-review-v3.md/json. Independently check current RAW before/after and original source/contract/production/canary assumptions, no premature site/package/chapter acceptance. Required receipt fields: verdict, materialization_verdict, required_repairs, report, report_sha256, input_manifest_sha256, approved_plan_sha256, approved_five_rows, raw_input_checks, exact_math_delta_only. No personal repaired pixel claim: second clean isolated build/browser and all22originals need fresh review afterward. Reused staged automated role/Astra-medium requested, history exposure/no human/external/absoluteblind/runtimeattestation as before.
''')
paths = {x for d in [RUN, CONTRACT] for x in d.rglob('*') if x.is_file() and '__pycache__' not in x.parts}
paths.update([PUBLIC, CANARY, PDF, CONTRIBUTION, ROOT / 'BanditRLProof.lean', ROOT / 'Tests.lean',
    *[ROOT / 'website/content' / n for n in ['chapters.json', 'readings.json', 'highlights.json']],
    *[Path(x['path']) for x in load(RUN / 'browser-generated-inputs-before-v1.json')['rows']]])
fixed()
write(RUN / 'render-repair-review-inputs-v3.json', dict(rows=rows(paths), exact_one_new_math_field=True,
    actual_failure_retained=True, whole_Goal_status='ACTIVE'))
print('Display failure retained and native repair recorded; exact one-field prospective review ready.')
