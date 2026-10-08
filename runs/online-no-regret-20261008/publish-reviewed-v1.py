from common_accepted_v1 import *
accepted_fixed()
assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed'
payload=load(RUN/'pr-payload-v1.json')
assert payload['body_sha256']==sha(payload['body_file']) and payload['draft']
for label in ['contributor-publication-v1','scoped-diff-publication-v5','source-scope-publication-v1']:
    assert load(RUN/(label+'-exit.json'))['exit_code']==0
owned=load(RUN/'owned-commit-paths-v2.json')
for command in [['git','add','--',*owned],['git','commit','-m','Accept reviewed no-regret reconciliation and preserve reader evidence']]:
    result=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print('\n'.join(result.stdout.decode('utf8',errors='replace').splitlines()[-5:]),flush=True)
    assert result.returncode==0,command
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
existing=json.loads(subprocess.check_output(['gh','pr','list','--state','all','--head',BRANCH,'--json','number,url,state']))
assert not existing,existing
gate('branch-push-v1','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','--set-upstream','origin',BRANCH)
assert subprocess.check_output(['git','ls-remote','origin','refs/heads/'+BRANCH],encoding='utf8').split()[0]==head
gate('draft-PR-create-v1','gh','pr','create','--draft','--base',payload['base'],'--head',payload['head'],'--title',payload['title'],'--body-file',payload['body_file'])
prs=json.loads(subprocess.check_output(['gh','pr','list','--state','open','--head',BRANCH,'--json','number,url,isDraft']))
assert len(prs)==1 and prs[0]['isDraft'],prs
pr=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/'+str(prs[0]['number'])]))
assert pr['head']['sha']==head and pr['base']['ref']==BASE_BRANCH and pr['state']=='open' and pr['draft'] and not pr['merged']
assert pr['body'].replace('\r\n','\n').strip()==Path(payload['body_file']).read_text(encoding='utf8').strip()
write(RUN/'created-PR-v1.json',pr)
print(json.dumps(dict(PR=pr['html_url'],number=pr['number'],head=head,state='OPEN-DRAFT-unmerged',attachment_required=True,goal_complete=False)),flush=True)
