from common_accepted_v1 import *
accepted_fixed()
receipt=load(RUN/'publication-repair-receipt-v4.json')
assert receipt['actor']['task']=='/root/source_reviewer'
assert receipt['verdict'] in ['accepted','accepted-with-explicit-delta'] and not receipt['required_repairs']
assert sha(receipt['report'])==receipt['report_sha256']
reviewed={x['path']:x['sha256'] for x in receipt['reviewed_files']}
for row in load(RUN/'publication-repair-review-inputs-v4.json')['rows']:
 assert sha(row['path'])==row['sha256']==reviewed[row['path']],row['path']
write(RUN/'publication-repair-accepted-v4.json',dict(status='accepted metadata repair',review_receipt_sha256=sha(RUN/'publication-repair-receipt-v4.json'),original_FINAL_unchanged=True,raw_audit_v1_failure_preserved=True,raw_audit_v2_actual_success=True,full_harness_final_actual_success=True,PR_prose_repairs=['seed-expected regret explicit','decoder reconstructs; reviewer accepts'],source_subobligation='C1-LOG-UNAVOIDABLE',source_closures_total_this_package=1,new_mathematical_progress_in_this_repair=0,chapter_complete=False,goal_complete=False,PR_delivery_pending=True))
native('publication-PR-prose-repair-event-v4','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(reason='Independent publication review rejected two PR prose ambiguities',evidence=(RUN/'publication-repair-receipt-v3.json').as_posix(),source_terminals_unchanged=True)))
native('publication-PR-prose-recandidate-event-v4','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(reason='PR-body-v2 explicitly states seed expectation and distinct actor authority',evidence=(RUN/'publication-repair-review-inputs-v4.json').as_posix(),source_terminals_unchanged=True)))
native('publication-repair-accepted-event-v4','lifecycle-event','--session',TASK,'--event','accepted','--payload-json',json.dumps(dict(reason='Separate publication repair review passed',evidence=(RUN/'publication-repair-receipt-v4.json').as_posix(),accepted_source_scope_only='C1-LOG-UNAVOIDABLE',no_new_proof_progress=True,chapter_complete=False,goal_complete=False)))
gate('origin-refresh-publication-v4','git','fetch','origin')
basepr=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/190']))
assert basepr['state']=='open' and not basepr['merged'] and basepr['head']['sha']==BASE
assert subprocess.check_output(['git','rev-parse','origin/'+BASE_BRANCH],encoding='utf8').strip()==BASE
write(RUN/'stacked-base-refresh-v4.json',dict(number=190,url=basepr['html_url'],state=basepr['state'],draft=basepr['draft'],merged=basepr['merged'],head=basepr['head']['sha'],origin_main=subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf8').strip()))
gate('contributor-publication-v4',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
assert 'affected production paths: 5' in (RUN/'contributor-publication-v4.log').read_text(encoding='utf8')
gate('scoped-diff-publication-v4',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','publication-v4')
gate('source-scope-publication-v4',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','publication-v4')
accepted_fixed()
owned=load(RUN/'owned-commit-paths-v1.json')
for cmd in [['git','add','--',*owned],['git','commit','-m','Resolve reviewed publication wording and preserve raw evidence audit']]:
 child=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);print('\n'.join(child.stdout.decode('utf8',errors='replace').splitlines()[-4:]),flush=True);assert child.returncode==0,cmd
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
existing=json.loads(subprocess.check_output(['gh','pr','list','--state','all','--head',BRANCH,'--json','number,url,state']))
assert not existing,existing
gate('branch-push-v1','git','push','--set-upstream','origin',BRANCH)
assert subprocess.check_output(['git','ls-remote','origin','refs/heads/'+BRANCH],encoding='utf8').split()[0]==head
payload=load(RUN/'pr-payload-v2.json')
gate('draft-PR-create-v1','gh','pr','create','--draft','--base',payload['base'],'--head',payload['head'],'--title',payload['title'],'--body-file',payload['body_file'])
prs=json.loads(subprocess.check_output(['gh','pr','list','--state','open','--head',BRANCH,'--json','number,url,isDraft']))
assert len(prs)==1 and prs[0]['isDraft'],prs
pr=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/'+str(prs[0]['number'])]))
assert pr['head']['sha']==head and pr['base']['ref']==BASE_BRANCH and pr['state']=='open' and pr['draft'] and not pr['merged']
assert pr['body'].replace('\r\n','\n').strip()==Path(payload['body_file']).read_text(encoding='utf8').strip()
write(RUN/'created-PR-v1.json',pr)
print(json.dumps(dict(PR=pr['html_url'],number=pr['number'],head=head,state='OPEN-DRAFT-unmerged',attachment_required=True,goal_complete=False)),flush=True)
