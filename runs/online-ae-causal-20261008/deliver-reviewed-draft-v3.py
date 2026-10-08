from common_accepted_v3 import *
from commit_owned_v1 import commit_owned

accepted_fixed()
post=load(RUN/'post-native-receipt-v2.json')
assert post['verdict'] in ['accepted','accepted-with-explicit-delta']
assert post['inputs_unchanged'] and not post['required_blocking_repairs']
assert post['report_sha256']==sha(RUN/'post-native-review-v2.md')
assert all(sha(r['path'])==r['sha256'] for r in load(RUN/'post-native-review-inputs-v2.json')['rows'])
assert (RUN/'accepted-source-commit-v3.json').exists()
commit_owned('Bind reviewed AE acceptance source commit and contributor evidence')
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
gate('reviewed-draft-push-v3','git','-c','credential.helper=',
    '-c','credential.helper=!gh auth git-credential','push','-u','origin',BRANCH)
title=(RUN/'prospective-PR-title-v2.txt').read_text(encoding='utf8').strip()
gate('reviewed-draft-create-v3','gh','pr','create','--draft','--base','codex/research-online-c1-core-audit',
    '--head',BRANCH,'--title',title,'--body-file',RUN/'prospective-PR-body-v2.md')
url=(RUN/'reviewed-draft-create-v3.log').read_text(encoding='utf8').strip()
assert url.startswith('https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pull/')
gate('reviewed-draft-remote-v3','gh','pr','view',url,'--json',
    'number,url,title,body,state,isDraft,headRefOid,baseRefName,headRefName,mergedAt')
r=load(RUN/'reviewed-draft-remote-v3.log')
assert r['headRefOid']==head and r['headRefName']==BRANCH
assert r['baseRefName']=='codex/research-online-c1-core-audit'
assert r['state']=='OPEN' and r['isDraft'] and r['mergedAt'] is None
assert r['title']==title
assert r['body'].replace('\r\n','\n').rstrip('\n')==(RUN/'prospective-PR-body-v2.md').read_text(encoding='utf8').replace('\r\n','\n').rstrip('\n')
write(RUN/'actual-draft-delivery-v3.json',dict(PR=r['number'],url=url,verified_delivery_head=head,
    exact_base=BASE,basePR=197,base_branch=r['baseRefName'],branch=BRANCH,state=r['state'],draft=True,
    merged=False,main_unchanged=True,live=False,
    actual_reviewed_title_sha256=sha(RUN/'prospective-PR-title-v2.txt'),
    actual_reviewed_body_sha256=sha(RUN/'prospective-PR-body-v2.md'),
    official_app_attachment_pending=True,remote_CI_not_yet_verified=True,
    chapter_complete=False,goal_complete=False,worktree_preserved=ROOT.as_posix(),
    note='Binds actual creation head; later scoped delivery-evidence commit may advance remote head.'))
print('Actual reviewed OPEN draft created:',url,'verified head',head,'official attachment required next.',flush=True)
