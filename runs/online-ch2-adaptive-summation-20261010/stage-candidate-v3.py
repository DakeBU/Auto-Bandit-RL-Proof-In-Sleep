from candidate_guard_v3 import *
candidate_fixed()
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==BASE
# Existing index is exactly the failed scoped stage; reject any outside path before restaging.
for p in subprocess.check_output(['git','diff','--cached','--name-only',BASE],encoding='utf8').splitlines():
    assert any(p==s or p.startswith(s+'/') for s in load(PLAN)['stage']),p
capture('candidate-stage-v3','git','add',*load(PLAN)['stage'])
changed,bindings=exact_cached_scope()
capture('candidate-staged-full-BASE-whitespace-v3','git','diff','--cached',BASE,'--check')
write(RUN/'candidate-stage-inspected-v3.json',dict(actual_changed_paths=changed,all_staged_blobs=bindings,old_changed_paths=OLD_ALLOWED,actual_full_BASE_whitespace_exit=0,scope='Scoped staging only. No commit/site/native acceptance or chapter closure.',chapter_complete=False,whole_Goal='active'))
candidate_fixed()
