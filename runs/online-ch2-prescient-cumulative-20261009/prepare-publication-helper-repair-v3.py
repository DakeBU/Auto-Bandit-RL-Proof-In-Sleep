from common import *
fixed()
r=load(RUN/'publication-plan-review-v2.json')
assert r['required_repairs'] and r['materialization_verdict'] not in ['accepted','accepted-with-explicit-delta']
for row in load(RUN/'publication-plan-review-inputs-v2.json')['rows']:
    assert sha(row['path'])==row['sha256'],row['path']
guard=(RUN/'publication_guard_v2.py').read_text(encoding='utf8').replace('publication-plan-review-v2.json','publication-plan-review-v3.json')
write(RUN/'publication_guard_v3.py',guard)
s=(RUN/'integrate-publication-v2.py').read_text(encoding='utf8').replace('publication-plan-review-v2.json','publication-plan-review-v3.json').replace('publication_guard_v2','publication_guard_v3')
old="for name in ['five-BODY-review-inputs-v1.json','publication-plan-review-inputs-v1.json']:"
new="""assert load(br)['input_manifest_sha256']==sha(RUN/'five-BODY-review-inputs-v1.json')
assert load(pr)['input_manifest_sha256']==sha(RUN/'publication-plan-review-inputs-v3.json')
for name in ['five-BODY-review-inputs-v1.json','publication-plan-review-inputs-v3.json']:"""
assert s.count(old)==1
s=s.replace(old,new)
write(RUN/'integrate-publication-v3.py',s)
for name in ['run-combined-gates','prepare-stage','commit-and-build-site','verify-registry','run-file-browser-capture']:
    oldp=RUN/(name+'-v1.py'); code=oldp.read_text(encoding='utf8').replace('publication_guard_v2','publication_guard_v3')
    if name=='commit-and-build-site': code=code.replace("RUN / 'verify-registry-v1.py'","RUN / 'verify-registry-v2.py'")
    write(RUN/(name+'-v2.py'),code)
write(RUN/'publication-helper-repair-v3.json',dict(prior_materialization_repair_review_sha256=sha(RUN/'publication-plan-review-v2.json'),exact_plan_v2_sha256=sha(CONTRACT/'exact-publication-plan-v2.json'),production_sha256=sha(PUBLIC),Test_sha256=sha(ROOT/'Tests/OnlinePrescientBregmanRegretCanary.lean'),only_helper_guard_binding_repair=True,operative_index_checked_before_any_write=True,BODY_and_operative_publication_index_SHA_receipt_bound=True,all_operative_rows_rehashed=True,unexecuted_v1_v2_helpers_preserved=True,whole_Goal_status='ACTIVE'))
write(RUN/'publication-plan-review-packet-v3.md','''# Narrow v3 executable binding repair; exact plan v2 unchanged

Read v2 repair verdict and v3 integration/guard/helper-repair. No formula, header, BODY, prospective path, reader field or source boundary changes. Exact plan remains exact-publication-plan-v2.json. Integration now checks BODY input manifest SHA against BODY accepted receipt, operative v3 input manifest SHA against this review receipt, and rehashes EVERY operative v3 and BODY row before first binding output/native command/canonical write. No old v1-only index reliance. Delayed conversion native capture/fill recipe remains exact v2; after actual command its OWN mutable journal delta is authorized output with contemporaneous beforebytes, not retroactively an unchanged review input. v1/v2 helpers remain unexecuted and preserved.

Review READ ONLY all indexed RAW and all32928baseline/PDF before/after; create-only publication-plan-review-v3.md/json. Fields verdict/materialization_verdict/required_repairs/approved_five_rows/approved_plan_sha256/input_manifest_sha256/report/hash. Approve only prospective five oldpaths plus OWN delayed conversion/contribution/evidence. Root/Tests/fullharness/contributor/shadow/sharedregistry/site/pixels/FINAL/native/delivery pending, source containers/chapter/Goal remain OPEN/ACTIVE. Distinct reused automated actor/history limits unchanged. Do not mutate any indexed file/native/roots/Git.
''')
paths=[p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
paths += [PUBLIC,ROOT/'Tests/OnlinePrescientBregmanRegretCanary.lean']+[Path(row['path']) for row in load(CONTRACT/'exact-publication-plan-v2.json')['rows']]
write(RUN/'publication-plan-review-inputs-v3.json',dict(rows=rows(paths),exact_plan_sha256=sha(CONTRACT/'exact-publication-plan-v2.json'),baseline_count=32928,allowed_new_outputs=['publication-plan-review-v3.md','publication-plan-review-v3.json'],no_canonical_mutation_yet=True,whole_Goal_status='ACTIVE'))
fixed()
print('Narrow v3 input-binding repair pinned, plan-v2 and all mathematics unchanged; no helper executed.')
