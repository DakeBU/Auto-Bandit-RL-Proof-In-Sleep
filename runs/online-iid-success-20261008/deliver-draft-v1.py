from common_accepted_v1 import *

accepted_fixed()
post=load(RUN/'post-native-receipt-v1.json')
assert post['verdict'] in ['accepted','accepted-with-explicit-delta'] and not post['required_blocking_repairs']
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
proposal=load(RUN/'proposed-publication-v1.json')
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
base_branch=proposal['base_branch']
remote=subprocess.check_output(['git','ls-remote','--heads','origin',base_branch],encoding='utf8').strip()
assert remote.split()[0]==BASE
gate('reviewed-draft-push-v1','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential',
    'push','-u','origin',BRANCH)
assert subprocess.check_output(['git','ls-remote','--heads','origin',BRANCH],encoding='utf8').split()[0]==head
gate('reviewed-draft-create-v1','gh','pr','create','--repo','DakeBU/Auto-Bandit-RL-Proof-In-Sleep',
    '--draft','--head',BRANCH,'--base',base_branch,
    '--title',Path(proposal['title_path']).read_text(encoding='utf8').rstrip('\n'),
    '--body-file',proposal['body_path'])
url=(RUN/'reviewed-draft-create-v1.log').read_text(encoding='utf8').strip().splitlines()[-1]
assert url.startswith('https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pull/')
gate('reviewed-draft-remote-state-v1','gh','pr','view',url,'--json',
    'number,url,state,isDraft,mergedAt,headRefName,headRefOid,baseRefName,baseRefOid,title,body')
pr=load(RUN/'reviewed-draft-remote-state-v1.log')
assert pr['state']=='OPEN' and pr['isDraft'] and pr['mergedAt'] is None
assert pr['headRefName']==BRANCH and pr['headRefOid']==head
assert pr['baseRefName']==base_branch and pr['baseRefOid']==BASE
assert pr['title']==Path(proposal['title_path']).read_text(encoding='utf8').rstrip('\n')
assert pr['body'].rstrip('\n')==Path(proposal['body_path']).read_text(encoding='utf8').rstrip('\n')
write(RUN/'actual-draft-delivery-v1.json',dict(PR=pr['number'],url=url,verified_delivery_head=head,
    exact_base=BASE,base_PR=195,base_branch=base_branch,branch=BRANCH,state='OPEN',draft=True,merged=False,
    reviewed_title_sha256=proposal['title_sha256'],reviewed_body_sha256=proposal['body_sha256'],
    official_app_attachment_pending=True,remote_CI_not_yet_verified=True,main_unchanged=True,live=False,
    chapter_complete=False,goal_complete=False,worktree_preserved=ROOT.as_posix(),
    note='Delivery receipts are added after the verified delivery point; subsequent bounded evidence commit may advance this PR head.'))
print(url)
print('Actual reviewed draft created; official app attachment and final evidence commit pending; whole Goal active.')
