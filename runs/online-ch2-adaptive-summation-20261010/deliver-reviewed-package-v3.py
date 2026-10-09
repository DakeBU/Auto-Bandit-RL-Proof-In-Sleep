from publication_guard_v1 import *

publication_fixed(after_native=True)
post = load(RUN/'post-native-review-v1.json')
review = load(RUN/'delivery-plan-review-v2.json')
for r in [post, review]:
    assert r['verdict'] in ['accepted', 'accepted-with-explicit-delta'] and not r['required_repairs']
    assert sha(r['report']) == r['report_sha256']
    assert sha(r['input_manifest']) == r['input_manifest_sha256']
assert post['post_native_verdict'] in ['accepted','accepted-with-explicit-delta']
assert review['delivery_plan_verdict'] == 'accepted'
assert review['approved_helper_sha256'] == sha(__file__)
assert review['approved_plan_sha256'] == sha(RUN/'delivery-plan-v2.json')
plan = load(RUN/'delivery-plan-v2.json')
prplan = load(RUN/'PR-plan-v1.json')
assert sha(prplan['body_path']) == prplan['body_sha256']
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip() == plan['candidate_head']
for row in load(review['input_manifest'])['rows']:
    assert sha(row['path']) == row['sha256'], row['path']

tail = ROOT/'tmp/online-ch2-adaptive-summation-delivery-v1'
assert not tail.exists()
tail.mkdir()

def obs(label, args):
    start = time.monotonic()
    p = subprocess.run(list(map(str,args)),cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    write(tail/(label+'.json'),dict(command=list(map(str,args)),actual_exit=p.returncode,cwd=ROOT.as_posix(),seconds=time.monotonic()-start,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii')))
    print(label,'actual exit',p.returncode,flush=True)
    assert p.returncode == 0,(label,p.stdout.decode('utf8',errors='replace'))
    return p.stdout.decode('utf8',errors='replace')

obs('fresh-fetch',['git','fetch','origin'])
assert not obs('canonical-status',['git','-C',str(ROOT.parent.parent/'research'),'status','--porcelain','--untracked-files=all']).strip()
parent = json.loads(obs('parent-PR215',['gh','pr','view','215','--json','number,url,state,isDraft,headRefName,headRefOid,mergedAt']))
assert parent['state']=='OPEN' and parent['isDraft'] and parent['mergedAt'] is None
assert parent['headRefOid']==BASE and parent['headRefName']==prplan['base']
existing = json.loads(obs('existing-PR',['gh','pr','list','--head',BRANCH,'--state','all','--json','number,url,state,headRefOid']))
assert existing == [],existing
allowed = {Path(r['path']).relative_to(ROOT).as_posix() for r in load(review['input_manifest'])['rows'] if Path(r['path']).is_relative_to(ROOT)} if hasattr(Path,'.is_relative_to') else {str(Path(r['path']).relative_to(ROOT)).replace('\\','/') for r in load(review['input_manifest'])['rows'] if str(Path(r['path'])).startswith(str(ROOT))}
allowed.update((RUN/p).relative_to(ROOT).as_posix() for p in ['delivery-plan-review-v2.md','delivery-plan-review-v2.json'])
dirty = subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines()
assert dirty
for line in dirty:
    assert line[3:] in allowed,line
obs('final-scoped-stage',['git','add',*load(PLAN)['stage']])
changed, bindings = exact_cached_scope()
obs('full-BASE-whitespace',['git','diff','--cached',BASE,'--check'])
for label, base in [('contributor-stack',BASE),('contributor-main','origin/main')]:
    out = obs(label,[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base])
    assert 'Contributor contract: N/A' not in out and MODULE.relative_to(ROOT).as_posix() in out
publication_fixed(after_native=True)
write(tail/'precommit-inspected.json',dict(changed_paths=changed,staged_blob_RAW_bindings=bindings,review_sha256=sha(RUN/'delivery-plan-review-v2.json'),post_native_review_sha256=sha(RUN/'post-native-review-v1.json'),full_BASE_whitespace_exit=0,both_contributors_nonempty=True,parent=parent))
obs('commit',['git','commit','-m',plan['commit_message']])
head = subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
publication_fixed(after_native=True)
obs('nonforce-push',['git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin','HEAD:refs/heads/'+BRANCH])
assert obs('remote-head',['git','ls-remote','origin','refs/heads/'+BRANCH]).split()[0] == head
url = obs('create-draft-PR',['gh','pr','create','--draft','--base',prplan['base'],'--head',BRANCH,'--title',prplan['title'],'--body-file',prplan['body_path']]).strip()
assert url.startswith('https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pull/'),url
pr = json.loads(obs('actual-PR',['gh','pr','view',url,'--json','number,url,state,isDraft,headRefName,headRefOid,baseRefName,title,body,mergedAt']))
assert pr['state']=='OPEN' and pr['isDraft'] and pr['mergedAt'] is None
assert pr['headRefOid']==head and pr['headRefName']==BRANCH and pr['baseRefName']==prplan['base']
expected_body = Path(prplan['body_path']).read_bytes().decode('utf8')
assert expected_body.endswith('\n') and not expected_body.endswith('\n\n') and '\r' not in expected_body
assert pr['title']==prplan['title'] and pr['body'] in [expected_body,expected_body[:-1]]
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
write(tail/'inspected.json',dict(delivered_head=head,remote_head=head,clean=True,PR=pr,official_app_attachment='pending: root must immediately call attach_artifact',distinct_actual_delivery_review='pending',source_site_commit=plan['candidate_head'],site_fresh_at_delivery_head=False,merge=False,deploy=False,chapter_complete=False,whole_Goal='active',worktree_disposition='retained for ongoing Goal'))
print('Delivered draft PR',url,'at',head,'; official attachment and actual delivery review pending.',flush=True)
