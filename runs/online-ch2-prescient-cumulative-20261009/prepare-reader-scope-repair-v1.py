from publication_guard_v3 import *
fixed()
triage = load(RUN / 'reader-scope-triage-v1.json')
old = 'Fixed steps allow T=0: empty sums and the derived identity x(0)=x0 give the zero-horizon endpoint. Variable steps require T>0 and nonincrease only between played rounds; the finite maximum is exactly over states0,...,T-1 and never includes x(T).'
new = 'The shared iterate_divergence_sum interface allows every natural horizon T, including T=0, and any schedule with eta_t>0 for t<T; it assumes no monotonicity. The fixed-step interfaces allow T=0 with a positive constant step. Only iterate_variable_sharp and iterate_variable_regret require T>0 and eta_(t+1)<=eta_t for t+1<T; their cap or finite maximum concerns previous states 0,...,T-1, not x(T).'
changes = []
plan = load(CONTRACT / 'exact-publication-plan-v2.json')
for fname, expected in [('highlights.json', 10), ('readings.json', 3)]:
    p = ROOT / 'website/content' / fname
    raw = p.read_bytes()
    assert raw.count(old.encode('utf8')) == expected
    after = raw.replace(old.encode('utf8'), new.encode('utf8'))
    before_p = RUN / ('reader-scope-before-' + fname)
    after_p = RUN / ('reader-scope-after-' + fname)
    write(before_p, raw)
    write(after_p, after)
    field_changes = []
    def compare(a, b, at=''):
        if isinstance(a, dict):
            assert a.keys() == b.keys()
            for k in a: compare(a[k], b[k], at + '/' + k)
        elif isinstance(a, list):
            assert len(a) == len(b)
            for i, v in enumerate(a): compare(v, b[i], at + '/' + str(i))
        elif a != b:
            assert isinstance(a, str) and a.count(old) == 1 and b == a.replace(old, new)
            field_changes.append(dict(field=at, before=a, after=b))
    compare(json.loads(raw), json.loads(after))
    assert len(field_changes) == expected
    changes.append(dict(path=p.as_posix(), before_snapshot=before_p.as_posix(), before_sha256=sha(before_p), after_snapshot=after_p.as_posix(), after_sha256=sha(after_p), fields=field_changes))
    row = next(r for r in plan['rows'] if r['path'] == p.as_posix())
    assert row['after_sha256'] == sha(before_p)
    row['after_snapshot'] = after_p.as_posix()
    row['after_sha256'] = sha(after_p)
    row['delta'] += ' Reader-scope repair: precisely enumerate shared, fixed, and variable interface assumptions.'
plan['reader_scope_repair'] = 'Only13 prose fields in the five newly added notes and one newly added card; math, proofs, links, old entries, all remaining fields immutable. Prior favorable reader review and failed SITEv1 evidence retained.'
write(CONTRACT / 'exact-publication-plan-v3.json', plan)
write(CONTRACT / 'reader-scope-repair-plan-v1.json', dict(rows=changes, exact_field_changes=13, old=old, new=new, full_plan_sha256=sha(CONTRACT / 'exact-publication-plan-v3.json'), mathematical_statement_change=False, whole_Goal_status='ACTIVE'))
guard = (RUN / 'publication_guard_v3.py').read_text(encoding='utf8')
needle = "    plan=CONTRACT/'exact-publication-plan-v2.json'\n    assert sha(plan)==binding['plan_sha256']"
replacement = "    repair=load(RUN/'reader-scope-repair-binding-v1.json')\n    review=load(RUN/'reader-scope-plan-review-v1.json')\n    assert sha(RUN/'reader-scope-plan-review-v1.json')==repair['review_sha256']\n    assert review['verdict'] in ['accepted','accepted-with-explicit-delta'] and not review['required_repairs']\n    assert sha(review['report'])==review['report_sha256']\n    plan=CONTRACT/'exact-publication-plan-v3.json'\n    assert sha(plan)==repair['plan_sha256']"
assert guard.count(needle) == 1
write(RUN / 'publication_guard_v4.py', guard.replace(needle, replacement).replace("SITE=ROOT/'tmp/online-ch2-prescient-cumulative-site-v1'", "SITE=ROOT/'tmp/online-ch2-prescient-cumulative-site-v2'"))
write(RUN / 'integrate-reader-scope-repair-v1.py', '''from publication_guard_v3 import *
fixed()
review=load(RUN/'reader-scope-plan-review-v1.json')
assert review['verdict'] in ['accepted','accepted-with-explicit-delta'] and not review['required_repairs']
assert sha(review['report'])==review['report_sha256']
assert review['input_manifest_sha256']==sha(RUN/'reader-scope-plan-inputs-v1.json')
for row in load(RUN/'reader-scope-plan-inputs-v1.json')['rows']: assert sha(row['path'])==row['sha256'],row['path']
mut=[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','trials.jsonl','own-artifact-journal.md']]
write(RUN/'pre-reader-repair-native-exact-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in mut]))
event('reader-scope-repair-native-v1','repair',dict(reason='Shared prose overrestricts arbitrary positive schedule divergence_sum;13 exact prose fields only.',proof_statement_change=False,source_container_closed=False,goal_complete=False))
plan=load(CONTRACT/'reader-scope-repair-plan-v1.json')
for row in plan['rows']:
    assert sha(row['path'])==row['before_sha256'] and sha(row['after_snapshot'])==row['after_sha256']
    Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
write(RUN/'reader-scope-repair-binding-v1.json',dict(review_sha256=sha(RUN/'reader-scope-plan-review-v1.json'),plan_sha256=sha(CONTRACT/'exact-publication-plan-v3.json'),exact_field_changes=13,source_statements_unchanged=True,original_SITEv1_and_reviews_retained=True,whole_Goal_status='ACTIVE'))
from publication_guard_v4 import fixed as repaired_fixed
repaired_fixed()
print('Only approved13 reader prose fields repaired; fresh site/pixels/FINAL pending.')
''')
write(RUN / 'reader-scope-plan-packet-v1.md', '''# Exact reader hypothesis-scope repair

Review ONLY prospective13 prose-field substitutions: ten in five NEW note plain/lean_notes; three in the one NEW source card plain/fallback/contract.assumptions. RAW replacement, recursive parsed exact diff and snapshots in reader-scope-repair-plan-v1. All math strings, Lean/header/BODY/pins, old entries/links, other fields unchanged. Original approved plan-v2 and failed reader/SITEv1 evidence remain preserved; triage supersedes old reader readiness. Full plan-v3 retains original five baseline paths with exactly two changed after snapshots; no new baseline mutation.

Review prospective guard-v4 and integrate-reader-scope-repair-v1: all actual review RAW/manifest checks before first output/native/canonical write, exact contemporaneous native-before bytes, actual OWN repair event, only approved two snapshot writes, then new guard. No retroactive stabilization/conversion, no source/Chapter closure. A new clean candidate site/registry/actual browser and root/distinct12original pixels/FINAL remain mandatory. Existing applicable complete Lean/fullharness inputs unchanged, so no fresh fullharness claim at later site head. Preserve all prior failures including OWN whitespace and stage helper partially executed before missing baseline file; do not call that failed helper unexecuted.

Independently hash indexed inputs and baseline with publication_guard_v3.fixed before/after. Create-only reader-scope-plan-review-v1.md/json with verdict, required_repairs, report/report_sha256/input_manifest_sha256,13exactfieldbindings and raw checks. Do not modify inputs/native/Git. Reused distinct automated source role/history disclosed; no human/external/absolute-blind/runtime attestation. All source containers/chapter/wholeGoal remain OPEN/ACTIVE.
''')
paths = {Path(r['path']) for r in load(RUN / 'reader-scope-triage-v1.json')['raw_input_checks']}
paths.update(p for d in [RUN, CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
paths.update([PUBLIC, CANARY, PDF, ROOT/'website/content/readings.json', ROOT/'website/content/highlights.json'])
write(RUN / 'reader-scope-plan-inputs-v1.json', dict(rows=rows(paths), exact_field_changes=13, no_materialization_yet=True, whole_Goal_status='ACTIVE'))
print('Exact13-field reader repair plan ready, not executed.')
