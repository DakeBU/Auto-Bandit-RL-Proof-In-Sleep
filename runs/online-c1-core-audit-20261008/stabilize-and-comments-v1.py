from common_v1 import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash

fixed()
receipt = RUN/'source-contract-receipt-v1.json'
report = RUN/'source-contract-review-v1.md'
assert sha(receipt) == 'b537220c23f410a7ce64e489e5a2ed13d6ffb43dedc5f9726c510edbc7cbf75c'
assert sha(report) == '3dc11aa992d304dcbb952e05d864bfa93b7dba9e794542791d6e5722764e41c1'
r = load(receipt)
assert r['verdict'] == 'accepted-with-explicit-delta' and not r['required_blocking_repairs']
assert r['fixed_input_count'] == 93 and not r['BODY_accepted'] and not r['source_package_accepted']
inputs = load(RUN/'source-contract-review-inputs-v1.json')['rows']
assert len(inputs) == 93
reviewed = {x['path']: x['sha256'] for x in r['reviewed_files']}
for x in inputs:
    assert sha(x['path']) == x['sha256'], x['path']
    assert reviewed[x['path']] == x['sha256'], x['path']
requirements = load(CONTRACT/'reader-requirements-v1.json')
assert r['reader_requirements'] == requirements
plan = load(CONTRACT/'exact-comment-plan-v1.json')
assert r['allowed_mutation_scope']['comments'] == plan['rows']
assert r['allowed_mutation_scope']['exact_comment_plan_sha256'] == sha(CONTRACT/'exact-comment-plan-v1.json')

mutable = MODULES + [Path('Tests.lean')] + [Path('website/content')/(n+'.json') for n in ['readings','highlights','chapters']]
snapshots = []
for p in mutable:
    q = RUN/'snapshots'/('CONTRACT-bound--'+p.as_posix().replace('/','--')+'.raw')
    write(q, p.read_bytes())
    snapshots.append(dict(path=p.as_posix(),original_sha256=sha(p),snapshot=q.as_posix(),snapshot_sha256=sha(q)))
rows = load(CONTRACT/'targets-v2.json')['targets']
write(RUN/'stabilized-contract-v2.json', dict(phase='stabilized',version=2,
    frozen_targets_sha256=sha(CONTRACT/'targets-v2.json'),terminal_headers=rows,
    source_sha256=PDF_SHA,review_receipt_sha256=sha(receipt),review_report_sha256=sha(report),
    reader_requirements=requirements,permitted_comment_plan_sha256=sha(CONTRACT/'exact-comment-plan-v1.json'),
    mutable_receipt_bound_snapshots=snapshots,existing_public_proofs=12,new_public_proofs=0,
    source_audits_pending=5,historical_Foundations_revalidation_preserved=True,
    BODY_pending=True,chapter_complete=False,goal_complete=False))
native('stabilized-event-v2','lifecycle-event','--session',TASK,'--event','stabilized',
    '--payload-json',json.dumps(dict(contract_version=2,contract=(RUN/'stabilized-contract-v2.json').as_posix(),
    source_review_receipt_sha256=sha(receipt),source_audits_pending=5,new_proofs=0)))
native('proving-event-v1','lifecycle-event','--session',TASK,'--event','proving',
    '--payload-json',json.dumps(dict(contract_version=2,ready_leaf='five-core-public-value-audit',
    terminal_fingerprint=sha(CONTRACT/'targets-v2.json'),edit_scope='approved five comments and one canary; no production proof/body/header edits',
    single_lower_route=True,new_proofs=0)))
for row in plan['rows']:
    p=Path(row['path']);raw=p.read_bytes()
    assert sha(p) == row['original_sha256']
    marker=b'namespace BanditRL.OnlineLearning'
    assert raw.count(marker) == 1
    result=raw.replace(marker,row['comment_utf8'].encode('utf8')+marker,1)
    assert hashlib.sha256(result).hexdigest() == row['result_sha256']
    p.write_bytes(result)
    assert p.read_bytes().replace(row['comment_utf8'].encode('utf8'),b'',1) == raw
for row in rows:
    header=lean_declaration_header(Path(row['path']),row['name'])
    assert header == row['header'] and statement_hash(header) == row['statement_hash']
write(RUN/'approved-comment-insertions-v1.json',dict(contract_receipt_sha256=sha(receipt),
    rows=plan['rows'],all_original_bytes_except_exact_insertions_preserved=True,
    twelve_full_headers_and_statement_hashes_unchanged=True,new_proofs=0,BODY_pending=True,
    source_audits_closed=0,chapter_complete=False,goal_complete=False))
write(RUN/'32_lower-proving-v1.md',
    'CONTRACT v2 accepted with exact source/API deltas. Exact five documentation insertions applied after immutable baseline snapshots; all old theorem/header/body bytes and twelve statement hashes unchanged. '
    'One test-only clipped fair infinite IID stream and globally clipped strict-past last-policy instantiate actual old proof values. '
    'Original seven Foundation canaries are reused, including positive leader switching and failure without either minimization or feasibility. '
    'No new production proof count. Fresh canaries/kernel/VALUE/BODY/combined/readers/FINAL/native/delivery remain required; five audit obligations still pending. '
    'Historical Foundation acceptance is preserved. Full source model/16 objects/null total/C1/C2/C3-16/appendix Goal remains active.')
print('Actual CONTRACT stabilized v2; exact reviewed comment insertions and original proof bytes verified. Canary/BODY/full acceptance remain pending.')
