from commit_owned_v1 import *

post_fixed()
d=load(RUN/'actual-draft-created-v1.json')
attachment=load(RUN/'official-app-attachment-v1.json')
assert attachment['url']==d['url'] and not attachment['actual_isError']
number=int(d['url'].rstrip('/').split('/')[-1])
gate('reviewed-draft-remote-v1','gh','pr','view',str(number),'--json',
    'number,url,title,body,state,isDraft,headRefOid,headRefName,baseRefName,mergedAt,statusCheckRollup')
actual=load(RUN/'reviewed-draft-remote-v1.log')
assert actual['number']==number and actual['url']==d['url']
assert actual['headRefOid']==d['creation_head'] and actual['headRefName']==BRANCH
assert actual['baseRefName']=='codex/research-online-c1-source-reconcile'
assert actual['state']=='OPEN' and actual['isDraft'] and actual['mergedAt'] is None
assert actual['title']==(RUN/'prospective-PR-title-v1.txt').read_text(encoding='utf8').strip()
assert actual['body'].replace('\r\n','\n').rstrip('\n')==(RUN/'prospective-PR-body-v1.md').read_text(encoding='utf8').rstrip('\n')
write(RUN/'actual-draft-delivery-v1.json',dict(PR=number,url=d['url'],
    verified_delivery_head=actual['headRefOid'],branch=BRANCH,basePR=201,exact_base=BASE,
    official_app_attachment_completed=True,remote_CI_certified=False,
    remote_checks_capture=actual['statusCheckRollup'],merged=False,live=False,
    chapter_complete=False,goal_complete=False))
print('Actual OPEN draft PR',number,'exact reviewed creation head and official attachment verified.',flush=True)
