from candidate_guard_v1 import *
candidate_fixed()
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==BASE
assert not subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').strip()
capture('candidate-stage-v1','git','add',*load(PLAN)['stage'])
changed,bindings=exact_cached_scope()
capture('candidate-staged-full-BASE-whitespace-v1','git','diff','--cached',BASE,'--check')
write(RUN/'candidate-stage-inspected-v1.json',dict(actual_changed_paths=changed,all_staged_blobs=bindings,old_changed_paths=OLD_ALLOWED,actual_full_BASE_whitespace_exit=0,scope='Scoped staging only. No commit/site/native acceptance or chapter closure.',chapter_complete=False,whole_Goal='active'))
candidate_fixed()
