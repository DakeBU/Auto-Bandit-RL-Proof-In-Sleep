from common_nonsmooth_publication_v2 import *
import base64,copy

fixed()
for label in ['nonsmooth-manifest-repair-commit-v1','nonsmooth-contributor-stack-v3','nonsmooth-contributor-main-v3','nonsmooth-site-build-v1']:
    p=ROOT/'tmp'/(TASK+'-'+label+'.json');write(RUN/(label+'.json'),p.read_bytes())
failed=load(RUN/'nonsmooth-site-build-v1.json')
message=base64.b64decode(failed['stdout_base64']).decode('utf8')
aux='BanditRL.OnlineConvex.hinge_convex_differentiable_iff._simp_1_1'
assert failed['actual_exit']==1 and aux in message and 'missing_highlight_dependencies' in message
old=load(RUN/'nonsmooth-reader-proposal-v2.json');new=copy.deepcopy(old)
assert new['notes'][1]['dependencies'].count(aux)==1
new['notes'][1]['dependencies'].remove(aux)
write(RUN/'nonsmooth-reader-proposal-v3.json',new)
highlight=ROOT/'website/content/highlights.json';before=load(highlight);after=copy.deepcopy(before)
entries=after if isinstance(after,list) else after['highlights']
note=next(n for n in entries if n['full_name']=='BanditRL.OnlineConvex.hinge_convex_differentiable_iff')
assert note==old['notes'][1];note['dependencies'].remove(aux)
assert note==new['notes'][1]
snapshot=RUN/'nonsmooth-highlights-link-repair-v3.json'
write(snapshot,after)
write(RUN/'nonsmooth-site-failure-classification-v1.json',dict(actual_command_receipt_sha256=sha(RUN/'nonsmooth-site-build-v1.json'),
    actual_exit=1,actual_message=message,classification='reader-public-registry-auxiliary-link-mismatch',
    auxiliary=aux,repair='Remove exactly one compiler-generated auxiliary name from the reader teaching-link array; retain all actual compiled TYPE/VALUE evidence, public parents, proof text, source and assumptions.',
    candidate_head='261df3132b55855aa73e4499ab981a1115f15319',
    original_failed_site_preserved=SITE.as_posix(),full_Lean_gate_still_applicable=True,
    mathematical_repair=False,review_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
plan=dict(before_proposal_sha256=sha(RUN/'nonsmooth-reader-proposal-v2.json'),after_proposal_sha256=sha(RUN/'nonsmooth-reader-proposal-v3.json'),
    removed_teaching_link=aux,mutable_path=highlight.as_posix(),before_sha256=sha(highlight),after_snapshot=snapshot.as_posix(),after_sha256=sha(snapshot),
    all_other_proposal_fields_unchanged=True,all_other_reader_AST_nodes_unchanged=True,
    proof_source_CANARY_root_unchanged=True,site_output_v2=(ROOT/'tmp/online-ch2-nonsmooth-site-v2').as_posix(),
    registry_policy_unchanged=True,complete_compiled_graph_retained=True,independent_review_pending=True,
    chapter_complete=False,whole_Goal_status='ACTIVE')
write(CONTRACT/'nonsmooth-reader-link-repair-plan-v3.json',plan)
inputs=[PUBLIC,CANARY,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',highlight,
    ROOT/'website/content/chapters.json',ROOT/'website/content/readings.json',
    CONTRACT/'nonsmooth-reader-link-repair-plan-v3.json',RUN/'nonsmooth-reader-proposal-v2.json',RUN/'nonsmooth-reader-proposal-v3.json',snapshot,
    RUN/'nonsmooth-reader-repair-review-v2.json',RUN/'nonsmooth-production-BODY-review-v1.json',RUN/'nonsmooth-canary-publication-review-v1.json',
    RUN/'nonsmooth-compiled-graph-inspected-v1.json',RUN/'nonsmooth-compiled-selected-graph-data-v2.json',
    RUN/'nonsmooth-full-harness-inspected-v1.json',RUN/'nonsmooth-site-build-v1.json',RUN/'nonsmooth-site-failure-classification-v1.json',
    ROOT/'website/scripts/build_site.py',RUN/'nonsmooth-contributor-stack-v3.json',RUN/'nonsmooth-contributor-main-v3.json']
write(RUN/'nonsmooth-reader-link-repair-review-input-v3.json',dict(files=rows(inputs),scope=plan,
    requested_actor='/root/source_reviewer',requested_effort='medium',runtime_attested=False,
    exclude_FINAL_pixel_and_delivery_acceptance=True))
fixed()
print('Exact one-link repair proposed, canonical readers untouched, frozen actual inputs ready for distinct review.')
