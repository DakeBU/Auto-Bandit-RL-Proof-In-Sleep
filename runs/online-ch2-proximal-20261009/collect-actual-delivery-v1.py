from publication_guard_v2 import *
fixed();delivery=ROOT/'tmp/online-ch2-proximal-delivery-v1'
actual=load(delivery/'inspected.json')
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert head==actual['actual_head']==actual['actual_remote_head'] and actual['actual_clean']
assert actual['PR']['number']==208 and actual['PR']['state']=='OPEN' and actual['PR']['isDraft'] and actual['PR']['mergedAt'] is None
assert actual['PR']['baseRefName']=='codex/research-online-ch2-prescient' and actual['stacked_exact_base']==BASE
assert not load(RUN/'official-PR208-attachment-v1.json')['actual_result']['isError']
copied=[]
for p in sorted(delivery.glob('*.json')):
    q=RUN/('actual-delivery-v1-'+p.name);write(q,p.read_bytes())
    copied.append(dict(original=p.as_posix(),durable_copy=q.as_posix(),exact_sha256=sha(p)));assert sha(p)==sha(q)
for row in load(RUN/'post-native-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256'],row['path']
write(RUN/'actual-delivery-summary-v1.json',dict(actual=actual,exact_copied_receipts=copied,official_attachment_sha256=sha(RUN/'official-PR208-attachment-v1.json'),post_native_review_sha256=sha(RUN/'post-native-review-v1.json'),source_candidate_site_commit='3a81dd6ae283fce90b849d928c18094f37b6d3b7',site_fresh_at_delivered_head=False,all_post_native_review_inputs_unchanged=True,distinct_delivery_review_PENDING=True,prospective_final_commit='Only new OWN RUN actual delivery evidence/review and exact RAW snapshots; no existing math/reader/native mutation',chapter_complete=False,whole_Goal_status='ACTIVE'))
write(RUN/'actual-delivery-packet-v1.md','''# Actual PR208 delivery review

Independently verify precise durable copies of ignored delivery receipts, actual clean delivered head equals remote/OPENdraft unmerged PR208 exact title/body/base/head, parentPR205 exact29086b6f3a033f6536054f4d9a06ae0e9b2f8a91, two current nonempty contributor gates, final staged scope, full2/scoped0 exact2immutable EOF files and preserved CRLF RAW differences. Official successful attach tool result is durably bound. Check FINAL/post-native source/proof/reader/native inputs still match through exact historical/native transitions, no further existing edits. Root publication_guard_v2.fixed() is not enough: independently hash each actual-delivery input before/after. New preview service was policy-rejected; file rendering succeeded and no HTTP/live/laterheadsitefresh claim.

Review final-evidence-delivery-v1.py: ONLY currently new OWN RUN delivery artifacts, review outputs and exact RAW snapshot may be committed/pushed, then ignored terminal observations compare new remote/PR head and unchanged title/body/base/draft/unmerged. No source/reader/native change, no self-referential evidence loop, no merge/deploy/retirement/global credentials. Actual accepted helper1->0 is not Chapter2 or full source completion; all8forwards/generalprescient REQUIRED/OPEN, whole16GoalACTIVE.

Create-only actual-delivery-review-v1.md/json with verdict, actual_delivery_verdict, prospective_evidence_only_commit_verdict, required_repairs, report/input hashes and independent RAW before/after checks, actual delivered head/PR/official attachment bindings. Reviewer must not publish or modify current inputs. Requested distinct staged automated Astra/medium role; no human/external/runtime attestation.
''')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update(Path(r['path']) for r in load(RUN/'post-native-inputs-v1.json')['rows'])
write(RUN/'actual-delivery-review-inputs-v1.json',dict(rows=rows(paths),delivered_head=head,PR=208,scope='Actual scoped draftPR delivery and prospective evidence-only final commit; general source/Chapter2/wholeGoal remain open',chapter_complete=False,whole_Goal_status='ACTIVE'))
print('Actual PR208 delivery evidence durably copied; distinct review pending at',head)
