from common_accepted_v2 import *

accepted_fixed()
post=load(RUN/'post-native-receipt-v2.json')
assert post['verdict'] in ['accepted','accepted-with-explicit-delta'] and not post['required_blocking_repairs']
assert post['inputs_unchanged']
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
title=RUN/'prospective-PR-title-v2.txt';body=RUN/'prospective-PR-body-v2.md'
reviewed={x['path']:x['sha256'] for x in load(RUN/'FINAL-review-inputs-v2.json')['rows']}
assert reviewed[title.as_posix()]==sha(title) and reviewed[body.as_posix()]==sha(body)
base_branch='codex/research-online-iid-success'
assert subprocess.check_output(['git','ls-remote','--heads','origin',base_branch],encoding='utf8').split()[0]==BASE
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
gate('reviewed-draft-push-v2','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin',BRANCH)
assert subprocess.check_output(['git','ls-remote','--heads','origin',BRANCH],encoding='utf8').split()[0]==head
gate('reviewed-draft-create-v2','gh','pr','create','--repo','DakeBU/Auto-Bandit-RL-Proof-In-Sleep','--draft',
    '--head',BRANCH,'--base',base_branch,'--title',title.read_text(encoding='utf8').rstrip('\n'),'--body-file',body)
url=(RUN/'reviewed-draft-create-v2.log').read_text(encoding='utf8').strip().splitlines()[-1]
assert url.startswith('https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pull/')
gate('reviewed-draft-remote-state-v2','gh','pr','view',url,'--json','number,url,state,isDraft,mergedAt,headRefName,headRefOid,baseRefName,baseRefOid,title,body')
pr=load(RUN/'reviewed-draft-remote-state-v2.log')
assert pr['state']=='OPEN' and pr['isDraft'] and pr['mergedAt'] is None
assert pr['headRefName']==BRANCH and pr['headRefOid']==head and pr['baseRefName']==base_branch and pr['baseRefOid']==BASE
assert pr['title']==title.read_text(encoding='utf8').rstrip('\n') and pr['body'].rstrip('\n')==body.read_text(encoding='utf8').rstrip('\n')
write(RUN/'actual-draft-delivery-v2.json',dict(PR=pr['number'],url=url,verified_delivery_head=head,exact_base=BASE,basePR=196,
    base_branch=base_branch,branch=BRANCH,state='OPEN',draft=True,merged=False,main_unchanged=True,live=False,
    actual_reviewed_title_sha256=sha(title),actual_reviewed_body_sha256=sha(body),official_app_attachment_pending=True,
    remote_CI_not_yet_verified=True,chapter_complete=False,goal_complete=False,worktree_preserved=ROOT.as_posix(),
    note='A later bounded delivery-evidence commit may advance the PR head; this record binds the actual verified creation point.'))
print(url)
