from commit_owned_v1 import *

post_fixed()
assert (RUN/'accepted-source-commit-v1.json').exists()
receipt=commit_owned('Bind reviewed FTL acceptance commit evidence','delivery-commit-v1')
head=receipt['actual_head']
gate('reviewed-draft-push-v1','git','-c','credential.helper=',
    '-c','credential.helper=!gh auth git-credential','push','-u','origin',BRANCH)
title=(RUN/'prospective-PR-title-v1.txt').read_text(encoding='utf8').strip()
gate('reviewed-draft-create-v1','gh','pr','create','--draft','--base','codex/research-online-kernel-causal',
    '--head',BRANCH,'--title',title,'--body-file',RUN/'prospective-PR-body-v1.md')
url=(RUN/'reviewed-draft-create-v1.log').read_text(encoding='utf8').strip()
assert url.startswith('https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pull/')
write(RUN/'actual-draft-created-v1.json',dict(url=url,creation_head=head,basePR=200,exact_base=BASE,
    branch=BRANCH,official_attachment_required_next=True,merged=False,live=False,goal_complete=False))
print('Created draft; immediate official app attachment required:',url,flush=True)
