from common_final_v9 import *
import base64
fixed()
out=ROOT/'tmp'
def encoded(path,args,required=True):
 p=subprocess.run(args,cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 write(path,dict(command=args,cwd=ROOT.as_posix(),actual_exit=p.returncode,stdout_base64=base64.b64encode(p.stdout).decode('ascii')))
 if required:assert p.returncode==0,(args,p.returncode)
 return p
before='14567d019c31f8f307ac5ab765144ae7d71f1ea1'
first=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert first.startswith('7a8e12e9') and subprocess.check_output(['git','rev-parse','HEAD^'],encoding='utf8').strip()==before
assert load(out/'online-c1-chapter-audit-final-delivery-commit-v1.json')['actual_exit']==0
status=subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8')
assert 'final-chapter-stage-final-v1.json' in status
write(RUN/'final-chapter-publication-repair-v2.md','Publication wrapper v1 actually exited1 AFTER successful metadata commit7a8e12e9 and BEFORE push. Its final git-add receipt was created after git add, leaving that own JSON untracked; the clean-check assertion correctly stopped publication. Mathematical/source/website inputs and accepted local gate are unchanged. The exact receipt and original failed helper are retained. V2 publishes an additional evidence-only commit; all outputs produced after its final staging command are ignored tmp files, so no recursively generated untracked receipt is omitted. This is a publication-wrapper repair, not a compiler failure or a retroactive successful v1 wrapper.')
scope=[RUN.relative_to(ROOT).as_posix()]
encoded(out/'online-c1-chapter-audit-final-delivery-stage-v2.json',['git','add','--',*scope])
exceptions=load(RUN/'post-native-RAW-exception-addendum-v5.json')['exact_RAW_exceptions']
allowed={Path(r['path']).relative_to(ROOT).as_posix() for r in exceptions}
p=encoded(out/'online-c1-chapter-audit-final-delivery-full-diff-v2.json',['git','diff','--cached',BASE,'--check'],False)
observed={s.split(':',1)[0] for s in p.stdout.decode('utf8').splitlines() if ': trailing whitespace.' in s or ': new blank line at EOF.' in s}
assert observed==allowed and p.returncode==2
for r in exceptions:assert sha(r['path'])==r['sha256']
encoded(out/'online-c1-chapter-audit-final-delivery-scoped-diff-v2.json',['git','diff','--cached',BASE,'--check','--','.',*[':(exclude)'+f for f in sorted(allowed)]])
encoded(out/'online-c1-chapter-audit-final-delivery-commit-v2.json',['git','commit','-m','Preserve final publication diagnostic and wrapper repair'])
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert subprocess.check_output(['git','rev-parse','HEAD^'],encoding='utf8').strip()==first
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
fixed()
encoded(out/'online-c1-chapter-audit-final-delivery-push-v1.json',['git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','origin',BRANCH])
beforepr=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/203'],encoding='utf8'))
body=(RUN/'PR-BODY-final-v3.md').read_text('utf8')
encoded(out/'online-c1-chapter-audit-final-delivery-body-v1.json',['gh','pr','edit','203','--body-file',str(RUN/'PR-BODY-final-v3.md')])
pr=json.loads(encoded(out/'online-c1-chapter-audit-final-delivery-PR203-API-v1.json',['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/203']).stdout.decode('utf8'))
assert pr['state']=='open' and pr['draft'] and not pr['merged'] and pr['head']['sha']==head and pr['base']['sha']==BASE and pr['base']['ref']=='codex/research-online-ftl-obstruction'
assert pr['title']==beforepr['title'] and pr['body'].strip()==body.strip()
remote=subprocess.check_output(['git','ls-remote','origin','refs/heads/'+BRANCH],encoding='utf8').split()[0];assert remote==head
canonical=subprocess.check_output(['git','-C','E:/ABRL/research','rev-parse','HEAD'],encoding='utf8').strip()
assert canonical==subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf8').strip()=='6847b678a73db68dee5101d6f05c2453c1405afc'
assert not subprocess.check_output(['git','-C','E:/ABRL/research','status','--porcelain'],encoding='utf8').strip()
encoded(out/'online-c1-chapter-audit-final-delivery-diff-v1.json',['git','diff',before,head,'--'])
encoded(out/'online-c1-chapter-audit-final-delivery-CI-v1.json',['gh','pr','checks','203','--json','name,state,link'],False)
write(out/'online-c1-chapter-audit-final-delivery-state-v1.json',dict(PR_url=pr['html_url'],actual_local_head=head,actual_remote_head=remote,previous_published_source_head=before,
 metadata_commit=first,evidence_only_repair_commit=head,wrapper_v1_actual_exit=1,wrapper_v2_actual_publication_succeeded=True,
 stack_base=BASE,stack_base_branch=pr['base']['ref'],title=pr['title'],draft=True,state='open',merged=False,
 published_body_sha256=sha(RUN/'PR-BODY-final-v3.md'),actual_published_body_matches=True,canonical_main=canonical,canonical_dirty=False,
 worktree_dirty=False,worktree_preserved_active=True,three_website_JSONs_unchanged=True,source_math_roots_Tests_pins_unchanged=True,
 actual_commit_push_success=True,whole_Goal_status='ACTIVE',final_distinct_exact_head_review_pending=True,main_live_updated=False,deployed=False,
 source_FINAL_sha256=sha(RUN/'FINAL-receipt-v1.json'),post_native_sha256=sha(RUN/'post-native-receipt-v1.json'),CI_not_certified=True))
paths={Path(r['path']) for r in load(RUN/'post-native-inputs-v1.json')['rows']}
paths.update(p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
paths.update(p for p in out.glob('online-c1-chapter-audit-final-delivery-*.json') if p.is_file())
assert all(p.is_file() for p in paths)
write(out/'online-c1-chapter-audit-final-delivery-inputs-v1.json',dict(phase='short distinct actual final-head/metadata delivery review',rows=rows(paths),actual_head=head,whole_Goal_status='ACTIVE',proof_total=None))
print('Actual final commits/push/body verified:',head,'; clean checkout; short distinct exact-head review next.',flush=True)
