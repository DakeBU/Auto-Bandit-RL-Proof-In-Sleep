from publication_guard_v2 import *
fixed()
bef=load(RUN/'contributor-schema-before-v3.json');raw=base64.b64decode(bef['before_raw_base64'])
assert hashlib.sha256(raw).hexdigest()==bef['before_sha256']
old=json.loads(raw.decode('utf8'));current=load(CONTRIBUTION)
assert current['verification']['focused_checks']==[old['verification']['focused_checks']]
check=json.loads(json.dumps(current));check['verification']['focused_checks']=check['verification']['focused_checks'][0]
assert check==old and load(RUN/'contributor-schema-repair-v3.json')['actual_exit']==0
write(RUN/'contributor-schema-wrapper-failure-v3.json',dict(observed_actual_exit=1,stage='After actual native repair event and successful OWN manifest type fix',error='Summary path collided with already existing capture receipt contributor-schema-repair-v3.json; create-only assertion stopped before gate v3 creation',source_Test_changes=False,repair='Resume only unexecuted summary/gate creation; do not rerun event or metadata edit',failed_script=rows([RUN/'repair-contributor-schema-v3.py'])))
write(RUN/'contributor-schema-repair-inspected-v3.json',dict(before_sha256=bef['before_sha256'],after_sha256=sha(CONTRIBUTION),only_change='verification.focused_checks: exact text -> singleton list of same text',all_words_preserved=True,root_Tests_full_harness_reuse='Actual source/root/Tests/pins unchanged; not a Lean failure',distinct_FINAL_review='pending',source_Test=rows([PUBLIC,TEST]),chapter_complete=False,whole_Goal='ACTIVE'))
s=(RUN/'commit-and-build-site-v2.py').read_text(encoding='utf8')
for label in ['candidate-stage-v2','candidate-full-package-diff-v2','exact-RAW-line-ending-snapshots-candidate-v2','candidate-diff-audit-v2','candidate-final-stage-v1','candidate-final-diff-v1','candidate-commit-v1','contributor-stack-v1','contributor-main-v1']:
    s=s.replace(label,label[:-2]+'v3')
s=s.replace('Prove causal unbounded OSD lower bound and source coefficient','Fix OSD contribution verification schema and retain gate evidence')
compile(s,'commit-and-build-site-v3.py','exec');write(RUN/'commit-and-build-site-v3.py',s)
fixed()
print('Already applied exact schema repair inspected; no repeated event/edit; resumed gate v3 ready.',flush=True)
