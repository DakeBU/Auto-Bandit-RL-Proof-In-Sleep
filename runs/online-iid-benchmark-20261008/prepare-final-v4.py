from common_integrated_v2 import *
from commit_owned_v2 import current_owned_paths

fixed_integrated()
r = load(RUN/'final-reader-receipt-v3.json')
assert r['actor']['task'] == '/root/source_reviewer' and r['verdict'] == 'rejected'
assert not r['required_mathematical_repairs'] and not r['required_blocking_reader_repairs']
assert r['fixed_input_count'] == 846
for row in load(RUN/'final-reader-inputs-v3.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
for row in load(CONTRACT/'reader-requirements-v2.json'):
    assert r['reader_requirement_verdicts'][row['id']]['verdict'] == 'satisfied'
write(RUN/'prospective-pr-title-v4.txt', (RUN/'prospective-pr-title-v3.txt').read_bytes())
write(RUN/'prospective-pr-body-v4.md', (RUN/'prospective-pr-body-v3.md').read_bytes())
text = (RUN/'proposed-publication-v3.md').read_text(encoding='utf8')
assert text.count('prospective-pr-title/body-v2') == 1
text = text.replace('prospective-pr-title/body-v2', 'prospective-pr-title/body-v4')
text += '\nThe v4 title/body bytes equal the corrected v3 prose, including v9 site and retained FINALv2 rejection. Rejected FINALv3/M1 is preserved; this v4 file is the sole operative prospective publication pointer. All previous v2/v3 publication files are historical only. Actual FINALv4/native acceptance is required before push/PR.\n'
write(RUN/'proposed-publication-v4.md', text)
assert sha(RUN/'prospective-pr-title-v4.txt') == sha(RUN/'prospective-pr-title-v3.txt')
assert sha(RUN/'prospective-pr-body-v4.md') == sha(RUN/'prospective-pr-body-v3.md')
write(RUN/'prospective-publication-repair-v4.json', dict(rejected_FINAL_report_sha256=sha(RUN/'final-reader-review-v3.md'),
    rejected_FINAL_receipt_sha256=sha(RUN/'final-reader-receipt-v3.json'), actual_M1='Historical proposed-publication-v3 selected obsolete title/body-v2.',
    repair='New versioned operative proposed-publication-v4 selects v4 title/body with rawbytes identical to correct v3 prose. Original wrong v3 inputs/rejection preserved.',
    original_v3_inputs_846_unchanged=True, no_mathematical_reader_site_change=True,
    current_v9_site_and_14_ROOT_and_distinct_reviewer_views_reused_by_exact_hash=True,
    actual_final_v4_required=True, native_acceptance=False, package_accepted=False, chapter_complete=False, goal_complete=False))
paths = current_owned_paths()
assert all(p.startswith(RUN.relative_to(ROOT).as_posix()+'/') for p in paths)
for start in range(0, len(paths), 48):
    child = subprocess.run(['git','-c','core.autocrlf=false','add','--']+paths[start:start+48], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert child.returncode == 0
for p in paths:
    assert subprocess.check_output(['git','show',':'+p]) == Path(p).read_bytes()
gate('scoped-diff-pre-FINAL-v4',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v7.py','pre-FINAL-v4')
mutable = [MANIFEST,Path('MANIFEST.md'),Path('runs/trials.jsonl'),Path('runs/lifecycle_sessions.jsonl'),Path('runs/lifecycle_memory.jsonl')]
mutable += [Path(folder)/(TASK+'.md') for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']]
snapshots = []
for p in mutable:
    snapshot = RUN/'snapshots'/('FINAL-review-v4-'+p.as_posix().replace('/','--')+'.raw')
    write(snapshot,p.read_bytes())
    snapshots.append(dict(live_path=p.as_posix(),snapshot=snapshot.as_posix(),sha256=sha(snapshot),
        future_update='Only own acceptance/delivery evidence fields and exact own-task journal/document appends; no source/proof/type/root/reader or other-task changes.'))
assert len(snapshots) == 10
write(RUN/'FINAL-metadata-snapshots-v4.json',snapshots)
packet = (RUN/'final-reader-packet-v3.md').read_text(encoding='utf8')
for old,new in [('final-reader-inputs-v3','final-reader-inputs-v4'),('final-reader-review-v3.md','final-reader-review-v4.md'),
    ('final-reader-receipt-v3.json','final-reader-receipt-v4.json'),('FINAL-metadata-snapshots-v3','FINAL-metadata-snapshots-v4')]:
    packet = packet.replace(old,new)
packet = '''# Metadata-only M1 repair: operative FINALv4

Read original rejected FINALv3 report/receipt: all846 inputs unchanged, ALL14 v9 originals actually independently viewed, F1/F2 and exactR1–R9 satisfied. Only M1 stale prospective-publication pointer remained. Proposed-publication-v4 is now SOLE OPERATIVE and selects prospective-pr-title/body-v4. Its title/body rawbytes are IDENTICAL to correct v3 prose (v9 site and rejected FINALv2 retained). All obsolete v2/v3 pointers/prose/receipts remain immutable historical evidence and are NOT future publication authorization. Inspect this exact versioned delta, require repair_verdicts.M1 satisfied plus F1/F2/R1–R9 still satisfied. No new math/reader/site change: rehash current14 v9 PNGs and reuse your actual independent original views recorded in rejected v3; no new rendering required. Exact current site source/gates unchanged. Native acceptance/push/PR has NEVER executed; prepared acceptance-v2/v3 helpers cannot bypass their rejected receipts. Actual FINALv4 must be accepted before preparation/use of corresponding v4 acceptance/delivery tools. Future exactly10 metadata snapshot resolutions now FINAL-metadata-snapshots-v4.json, same permitted field/appends, no reader waiver. Previous rejected FINAL778 reader bytes resolve solely through exact reader-before-semantic-repair-v6.json.raw; previous rejected FINAL846 rows remain entirely unchanged. Write ONLY final-reader-review-v4.md/final-reader-receipt-v4.json; bind every new index row+manifest+report before/after. Required mathematical/metadata/reader repair arrays must represent actual unresolved findings. No chapter/Goal/merge/live claim.

''' + packet
packet = packet.replace('Review prospective PR title/body and proposed-publication-v3', 'Review operative prospective-pr-title/body-v4 and proposed-publication-v4')
write(RUN/'final-reader-packet-v4.md',packet)
paths = [p.resolve().as_posix() for root in [CONTRACT,RUN] for p in sorted(root.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
paths += [p.resolve().as_posix() for p in [PUBLIC,CANARY,Path('BanditRLProof.lean'),Path('Tests.lean'),
    Path('website/content/readings.json'),Path('website/content/highlights.json'),Path('website/content/chapters.json'),PDF]+mutable]
paths += [Path(p).resolve().as_posix() for p in load(RUN/'draft-baseline-v1.json')['fixed_files']]
site = Path('tmp/online-iid-benchmark-site-v9'); registry=load(RUN/'registry-v9.json')
paths += [(site/p).resolve().as_posix() for p in ['site-manifest.json','books/registry.json','chapters/online-foundations/index.html',registry['module_path']]]
rows = [dict(path=p,sha256=sha(p)) for p in dict.fromkeys(paths)]
write(RUN/'final-reader-inputs-v4.json',dict(stage='FINAL',rows=rows,fixed_input_count=len(rows),
    original_CONTRACT_rows=186,original_BODY_rows=583,future_metadata_snapshots='FINAL-metadata-snapshots-v4.json',
    operative_publication='proposed-publication-v4.md',applicable_registry='registry-v9.json',applicable_pixels='pixel-review-v9.json',
    previous_rejected_FINALs_preserved=True,package_accepted=False,chapter_complete=False,goal_complete=False))
for row in rows:
    assert sha(row['path']) == row['sha256']
fixed_integrated()
print('FINALv4 actual raw rows:',len(rows),'; metadata-only M1 repair, acceptance pending.')
