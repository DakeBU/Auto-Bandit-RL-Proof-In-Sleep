from candidate_execution_guard_v2 import *
candidate_plan_fixed()
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==BASE
capture('candidate-restage-v2','git','add',*load(RUN/'candidate-stage-plan-v1.json')['stage'])
changed=exact_cached_scope()
capture('candidate-active-text-diff-v2','git','diff','--cached',BASE,'--check')
rawrows=[]
for rel in changed:
    raw=(ROOT/rel).read_bytes();blob=subprocess.check_output(['git','show',':'+rel])
    if raw!=blob:
        assert raw.replace(b'\r\n',b'\n')==blob,rel
        rawrows.append(dict(path=rel,raw_sha256=sha(ROOT/rel),git_blob_sha256=hashlib.sha256(blob).hexdigest(),raw_base64=base64.b64encode(raw).decode('ascii'),only_CRLF_to_LF=True))
write(RUN/'exact-RAW-line-ending-snapshots-candidate-v2.json',dict(rows=rawrows,scope='Exact RAW bytes differing from Git LF filtering, retained without reserialization.'))
write(RUN/'candidate-stage-inspected-v1.json',dict(actual_changed_paths=changed,old_changed_paths=load(RUN/'candidate-stage-plan-v1.json')['old_changed_paths'],actual_active_text_diff_exit=0,actual_diff_receipt_sha256=sha(RUN/'candidate-active-text-diff-v2.json'),prior_failed_text_check_sha256=sha(RUN/'candidate-active-text-diff-v1.json'),artifacts=sha(RUN/'candidate-binary-artifacts-bound-v1.json'),scope='Exact23CRLF recognition plus reviewed immutable binary artifacts; ordinary whitespace checks retained. Staged only, not committed. Full harness retry pending.',chapter_complete=False,whole_Goal='active'))
candidate_plan_fixed()
