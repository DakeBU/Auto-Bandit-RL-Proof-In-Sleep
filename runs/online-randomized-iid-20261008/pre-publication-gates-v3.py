from common_accepted_v3 import *
from commit_owned_v2 import stage_owned, commit_owned
import re

accepted_fixed()
post = reviewer_receipt('post-native-receipt-v4.json')
post_inputs = load(RUN/'post-native-review-inputs-v4.json')
assert post['inputs_unchanged'] and post['fixed_input_count'] == len(post_inputs['rows']) == 56
post_reviewed = {Path(x['path']).resolve().as_posix():x.get('sha256',x.get('sha256_raw_bytes')) for x in post['reviewed_files']}
for row in post_inputs['rows']:
    assert sha(row['path']) == post_reviewed[Path(row['path']).resolve().as_posix()] == row['sha256'], row['path']
stage_owned()
gate('source-scope-pre-publication-v3', sys.executable,'-B','-X','utf8',RUN/'audit-owned-scope-v2.py','pre-publication-v3')
gate('scoped-diff-pre-publication-v3', sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','pre-publication-v3')
commit_owned('Accept bounded private-seed IID producer with distinct FINAL and native evidence')
head = subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
gate('contributor-pre-publication-v3', sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
raw = (RUN/'contributor-pre-publication-v3.log').read_text(encoding='utf8')
assert 'affected production paths: 5' in raw and 'changed contribution contracts: 1' in raw
assert 'Contributor contract passed.' in raw
changed = re.search(r'^changed paths: (\d+)$',raw,re.M)
assert changed
actual_paths = subprocess.check_output(['git','diff','--name-only',BASE,head],encoding='utf8').splitlines()
assert int(changed.group(1)) == len(actual_paths) and len(actual_paths) > 5
write(RUN/'pre-publication-exact-gate-bindings-v3.json',dict(actual_source_head=head, exact_base=BASE,
    actual_changed_paths=len(actual_paths),production_paths=5,own_contribution_contracts=1,
    contributor_exit=0,post_native_receipt_sha256=sha(RUN/'post-native-receipt-v4.json'),
    FINAL_receipt_sha256=sha(RUN/'final-reader-receipt-v3.json'),
    applicable_Lean_site_by_unchanged_public_Test_pins_readers=True,
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    PR_delivery_pending=True,chapter_complete=False,goal_complete=False))
stage_owned()
gate('scoped-diff-publication-evidence-v3',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','publication-evidence-v3')
commit_owned('Record actual nonvacuous exact-base contributor gate before draft delivery')
accepted_fixed()
print('Clean exact publication head:',subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip())
