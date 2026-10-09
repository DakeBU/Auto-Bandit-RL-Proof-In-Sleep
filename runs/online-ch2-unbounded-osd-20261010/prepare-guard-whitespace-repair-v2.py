from common import *
fixed_before=RUN/'publication_guard_v1.py'
before=fixed_before.read_bytes();after=before.rstrip(b'\r\n')+b'\n'
assert before==after+b'\n'
write(RUN/'guard-whitespace-before-v1.json',dict(path=fixed_before.as_posix(),sha256=sha(fixed_before),before_raw_base64=base64.b64encode(before).decode('ascii')))
write(RUN/'guard-whitespace-after-v2.py.txt',after)
s=before.decode('utf8').rstrip()+'\n'
old="        for row in load(r['input_manifest'])['rows']:assert sha(row['path'])==row['sha256'],row['path']"
new="""        repair=load(RUN/'guard-whitespace-repair-review-v2.json')
        assert repair['verdict'] in ['accepted','accepted-with-explicit-delta'] and not repair['required_repairs']
        assert sha(repair['report'])==repair['report_sha256'] and sha(repair['input_manifest'])==repair['input_manifest_sha256']
        for rr in load(repair['input_manifest'])['rows']:assert sha(rr['path'])==rr['sha256'],rr['path']
        delta=load(RUN/'guard-whitespace-exact-plan-v2.json')
        assert repair['approved_plan_sha256']==sha(RUN/'guard-whitespace-exact-plan-v2.json')
        for row in load(r['input_manifest'])['rows']:
            if row['path']==delta['guard_path']:
                assert row['sha256']==delta['guard_before_sha256']
                raw=base64.b64decode(load(RUN/'guard-whitespace-before-v1.json')['before_raw_base64'])
                assert hashlib.sha256(raw).hexdigest()==row['sha256']
                assert sha(row['path'])==delta['guard_after_sha256']
            else:assert sha(row['path'])==row['sha256'],row['path']"""
assert s.count(old)==1;s=s.replace(old,new)
compile(s,'publication_guard_v2.py','exec');write(RUN/'publication_guard_v2.py',s)
transitions=[]
for name in ['publication_guard_v1.py','verify-registry-v1.py','prepare-browser-v1.py','run-file-browser-v1.py','prepare-FINAL-v1.py','record-native-acceptance-v1.py','prepare-post-native-v1.py']:
    p=RUN/name;raw=p.read_bytes()
    if name=='publication_guard_v1.py':newraw=after
    else:
        assert raw.count(b'from publication_guard_v1 import *')==1
        newraw=raw.replace(b'from publication_guard_v1 import *',b'from publication_guard_v2 import *')
    snap_before=RUN/('guard-repair-before-'+name+'.json')
    snap_after=RUN/('guard-repair-after-'+name+'.txt')
    write(snap_before,dict(path=p.as_posix(),sha256=sha(p),before_raw_base64=base64.b64encode(raw).decode('ascii')))
    write(snap_after,newraw)
    transitions.append(dict(path=p.as_posix(),before_sha256=sha(p),before_snapshot=snap_before.as_posix(),after_sha256=sha(snap_after),after_snapshot=snap_after.as_posix(),delta='One terminal LF removed only' if name=='publication_guard_v1.py' else 'One import version changed only; never-executed future helper'))
plan=RUN/'guard-whitespace-exact-plan-v2.json'
write(plan,dict(guard_path=fixed_before.as_posix(),guard_before_sha256=sha(fixed_before),guard_after_sha256=hashlib.sha256(after).hexdigest(),transitions=transitions,new_guard_sha256=sha(RUN/'publication_guard_v2.py'),old_review_manifests_immutable=True,old_33852_and_exact_five_publication_bytes_unchanged=True,source_Test_pins_statements_unchanged=True,Lean_rerun_required=False,reason='Only own Python guard metadata/whitespace/import versions change after successful Lean gate; no Lean/build source change'))
gate=(RUN/'commit-and-build-site-v1.py').read_text(encoding='utf8')
gate=gate.replace('from publication_guard_v1 import *','from publication_guard_v2 import *')
gate=gate.replace("write(RUN/'candidate-stage-plan-v1.json',dict(stage=stage,exact_old_transitions=load(CONTRACT/'exact-publication-plan-v1.json')['rows'],merge=False,deploy=False,retire=False))","assert load(RUN/'candidate-stage-plan-v1.json')['stage']==stage")
for label in ['candidate-stage-v1','candidate-full-package-diff-v1','exact-RAW-line-ending-snapshots-candidate-v1','candidate-diff-audit-v1']:
    gate=gate.replace(label,label[:-2]+'v2')
compile(gate,'commit-and-build-site-v2.py','exec');write(RUN/'commit-and-build-site-v2.py',gate)
write(RUN/'apply-guard-whitespace-repair-v2.py','''from common import *
r=load(RUN/'guard-whitespace-repair-review-v2.json')
assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
assert sha(r['report'])==r['report_sha256'] and sha(r['input_manifest'])==r['input_manifest_sha256']
for row in load(r['input_manifest'])['rows']:assert sha(row['path'])==row['sha256'],row['path']
p=RUN/'guard-whitespace-exact-plan-v2.json';plan=load(p)
assert r['approved_plan_sha256']==sha(p)
for row in plan['transitions']:
    assert sha(row['path'])==row['before_sha256']
    assert sha(row['after_snapshot'])==row['after_sha256']
from publication_guard_v1 import fixed as before_fixed
before_fixed()
for row in plan['transitions']:Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
from publication_guard_v2 import fixed as after_fixed
after_fixed()
write(RUN/'guard-whitespace-repair-applied-v2.json',dict(approved_plan_sha256=sha(p),exact_transitions=plan['transitions'],source_Test_pins_unchanged=True,old_review_manifests_immutable=True,not_Lean_failure=True,site_build_pending=True))
print('Exact reviewed own guard/whitespace repair applied; old reviewed RAW preserved.',flush=True)
''')
paths=[plan,RUN/'publication_guard_v2.py',RUN/'commit-and-build-site-v2.py',RUN/'apply-guard-whitespace-repair-v2.py',RUN/'guard-whitespace-before-v1.json',RUN/'guard-whitespace-after-v2.py.txt',RUN/'publication-plan-review-v1.json',RUN/'publication-plan-review-inputs-v1.json',RUN/'publication-review-binding-v1.json',RUN/'candidate-full-package-diff-v1.json',RUN/'full-harness-inspected-v1.json',PUBLIC,ROOT/'Tests/OnlineUnboundedOSDCanary.lean']
paths += [Path(r[k]) for r in transitions for k in ['before_snapshot','after_snapshot']]
write(RUN/'guard-whitespace-repair-inputs-v2.json',dict(rows=rows(paths),mutable_own_paths_before_review=transitions,source_Test_and_all_old_paths_unchanged=True,stage='Whitespace-only own-helper repair after actual candidate diffcheck failure; not new math'))
write(RUN/'guard-whitespace-repair-request-v2.md','''# Exact OWN guard whitespace/import repair

Actual gitdiff --check exited2 only publication_guard_v1.py newblanklineEOF. No commit/site yet; root/Tests/fullharness passed. Inspect exact seven OWN transitions: removeONEterminalLF fromhistorically reviewedv1guard, sixneverexecutedfuturehelpers changeONEimportv1->v2 only. PreserveoldRAWbase64/originalreviewmanifests immutable. Newv2guard retains allbaseline/frozen/publication checks and adds favorable hash-bound repair receipt/plan/immutable-input checks; ONLYoriginalv1guard row SHA is allowed to match approvedafter while exacthistoricalbeforeRAWrecovered. No blanket hash exception/assertionweakening or source/root/readers change. Exact5oldpathpublication bytes stayunchanged, allother33852baseline untouched. Review newapply helper and resumedcommit/site v2 (existing stageplan reused, failedreceiptv1not overwritten, successful labels freshv2). Package/FINAL/native/delivery stillpending; no newLean source change hence applicableLean gate retained.

Independently inspect all RAWinputs, live sevenbeforepaths and exactdiffs, own newguard/helper logic, fullbaselineexcept5approveddeltas. Outputcreateonlyguard-whitespace-repair-review-v2.md/json withverdict/required_repairs/report+SHA/inputmanifest+SHA/approved_plan_sha256/approved_helpers/RAWbeforeafter. Approve ONLY exactapplyhelpertransitions then newguard/resumedgate, notgeneralpublication/FINAL. RequestedAstra/medium,reusedstagedactor,nohuman/external/runtimeattestation. Do not edit inputs.
''')
print('Versioned whitespace guard repair exact plan prepared; no live helper changed.',flush=True)
