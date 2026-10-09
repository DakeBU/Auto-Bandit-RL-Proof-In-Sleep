from publication_guard_v1 import *
fixed()
rp=RUN/'RAW-format-review-v1.json'
assert sha(rp)=='5ef41dc60af5efde1cf8218efd53283ec39acd99bce3c5592c0297501a6862d0'
r=load(rp)
assert r['verdict']=='accepted-with-explicit-delta' and not r['required_repairs']
for row in load(RUN/'RAW-format-review-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256']
exceptions=r['approved_RAW_exceptions']
assert len(exceptions)==2
for row in exceptions:assert sha(row['path'])==row['sha256']
stage=load(RUN/'candidate-stage-plan-v1.json')['stage']
capture('candidate-stage-v2','git','add',*stage)
changed=subprocess.check_output(['git','diff','--cached','--name-only',BASE],encoding='utf8').splitlines()
basepaths={Path(x['path']).relative_to(ROOT).as_posix() for x in load(RUN/'baseline-v1.json')['rows']}
allowed_old={Path(x['path']).relative_to(ROOT).as_posix() for x in load(CONTRACT/'exact-publication-plan-v2.json')['rows']}
assert set(changed)&basepaths==allowed_old
for path in changed:assert any(path==a or path.startswith(a+'/') for a in stage),path
rc,out=capture('candidate-full-diff-check-v2','git','diff','--cached',BASE,'--check',required=False)
assert rc==2 and out.count(': trailing whitespace.')==2 and ': new blank line at EOF.' not in out
for row in exceptions:
    rel=Path(row['path']).relative_to(ROOT).as_posix()
    assert rel+':'+str(row['line'])+': trailing whitespace.' in out
paths=[Path(x['path']).relative_to(ROOT).as_posix() for x in exceptions]
capture('candidate-scoped-diff-check-v2','git','diff','--cached',BASE,'--check','--','.',*[':(exclude)'+x for x in paths])
rawrows=[]
for rel in subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').splitlines():
    p=ROOT/rel;raw=p.read_bytes();blob=subprocess.check_output(['git','show',':'+rel])
    if raw!=blob:
        assert raw.replace(b'\r\n',b'\n')==blob,rel
        rawrows.append(dict(path=rel,raw_sha256=sha(p),git_blob_sha256=hashlib.sha256(blob).hexdigest(),raw_base64=base64.b64encode(raw).decode('ascii'),only_CRLF_to_LF=True))
write(RUN/'exact-RAW-line-ending-snapshots-v1.json',dict(rows=rawrows,scope='Exact candidate staged RAW bytes where Git CRLF filtering differs; no JSON reserialization/hash substitution.'))
write(RUN/'candidate-diff-audit-v2.json',dict(actual_full_exit=rc,actual_scoped_exit=0,scoped_whitespace_gate_passed=True,changed_count=len(changed),changed_paths=changed,only_five_old_paths_changed=True,all_other_baseline_immutable=True,approved_RAW_exceptions=exceptions,RAW_review_sha256=sha(rp),full_diff_exit0_claim=False,no_Lean_source_Test_reader_exemption=True,whole_Goal_status='ACTIVE'))
fixed()
print('Exact2 immutable RAW diagnostics full2/scoped0 inspected; all proof/source/other files checked, scoped candidate ready.')
