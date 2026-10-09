from common_nonsmooth_roots_v1 import *

fixed()
assert load(RUN/'nonsmooth-combined-root-Tests-inspected-v1.json')['actual_root_Tests_passed']
assert sha(RUN/'nonsmooth-reader-repair-review-v2.json')=='bdf4567d876282b9d4936c87bfd9f8ebe55ca4438b49d049fab4289e639b6708'
r=load(RUN/'nonsmooth-reader-repair-review-v2.json')
assert r['verdict']=='accepted' and not r['required_repairs']
for row in r['raw_input_checks']:
    assert sha(row['path'])==row['before_sha256']==row['after_sha256']
assert r['approved_scope_sha256']==sha(CONTRACT/'nonsmooth-future-publication-scope-v2.json')
m=load(CONTRACT/'nonsmooth-materialized-future-bytes-v1.json')
assert m['rows']==r['approved_materialized_bytes']
for row in m['rows']:
    target=Path(row['path']);raw=Path(row['after_snapshot']).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==row['after_sha256']
    if target.suffix=='.lean':
        assert target.read_bytes()==raw
    else:
        assert sha(target)==row['before_sha256']
        target.write_bytes(raw)
write(RUN/'nonsmooth-publication-integration-v2.json',dict(
    actual_distinct_reader_repair_review_sha256=sha(RUN/'nonsmooth-reader-repair-review-v2.json'),
    exact_materialized_bytes_sha256=sha(CONTRACT/'nonsmooth-materialized-future-bytes-v1.json'),
    original_reader_v1_rejection_preserved=True,only_reviewed_three_reader_AST_deltas_applied=True,
    old_all_Book_ID_link_formula_card_note_subtrees_preserved=True,
    old_root_and_pins_preserved_except_exact_two_import_appends=True,
    current_full_harness_site_FINAL_delivery_PENDING=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
from common_nonsmooth_publication_v2 import fixed as published_fixed
published_fixed()
contribution=ROOT/'research-wiki/contribution-contracts/ONLINE-CH2-NONSMOOTH-20261009.json'
c=load(RUN/'nonsmooth-contribution-manifest-draft-v1.json')
proofgate=load(RUN/'nonsmooth-combined-root-Tests-inspected-v1.json')
c['semantic_roundtrip']['remaining_semantic_delta']='Distinct production CONTRACT/source qualification/BODY and five canary CONTRACT/BODY accepted. Reader-v1 sole intuition blocker retained, exact-v2 correction and materialized scope accepted in separate review. Three production and five Test full-file hashes unchanged. Reused staged automated actors requested Astra/medium; no human/external/absolute-blind/runtime attestation. '+c['truth_boundary']
c['progress_updates']['teaching_route']='updated: one source-qualified card/three new notes and one module glob on existing singleton-differentiability route; all old cards/IDs/links/formulas and other Book subtrees preserved by exact reviewed AST/byte plan.'
c['verification']['bandit_check']='Actual current combined root and Tests compiler markers passed: '+str([x['actual_cached_inclusive_success_jobs'] for x in proofgate['rows']])+'. Full harness still pending; compiler cached-inclusive jobs are not newly recompiled theorem counts.'
c['verification']['independent_review']='Distinct production CONTRACT/source qualification/BODY, five canary CONTRACT/BODY and exact-reader-v2 repair/materialized-scope review accepted at fixed hashes. Sole rejected reader-v1 preserved. FINAL/native/delivery still pending; no human/external/absolute-blind/runtime attestation.'
write(contribution,c)
retrieval=ROOT/'research-wiki/retrieval-index/ONLINE-CH2-NONSMOOTH-20261009.md'
text=(RUN/'nonsmooth-retrieval-index-draft-v1.md').read_text(encoding='utf8')
text+='\nCurrent update: exact reader-v2 repair/materialized scope accepted and applied; actual combined root/Tests compiler gates passed. Full harness, shadow, nonvacuous contributor, shared registry/site/pixels, FINAL/native/delivery remain pending.\n'
write(retrieval,text)
capture('nonsmooth-stage-reviewed-publication-v2','git','add','BanditRLProof.lean','Tests.lean',
    'website/content/chapters.json','website/content/readings.json','website/content/highlights.json',
    contribution.relative_to(ROOT).as_posix(),retrieval.relative_to(ROOT).as_posix())
published_fixed()
print('Exact accepted reader-v2 publication and scoped canonical contribution/retrieval integrated; full harness/FINAL/site/delivery still pending.')
