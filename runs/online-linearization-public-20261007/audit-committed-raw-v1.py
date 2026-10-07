"""Audit all current run nonignored raw bytes against actual committed Git blobs."""
from common_v2 import *
root=Path('.').resolve();head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip();rows=[];ignored=[]
entries=subprocess.check_output(['git','ls-tree','-r','-z',head,'--',RUN.resolve().relative_to(root).as_posix()]).split(b'\0')
objects={e.split(b'\t',1)[1].decode('utf-8'):e.split(b'\t',1)[0].split()[2].decode('ascii') for e in entries if e}
for p in sorted(RUN.rglob('*')):
 if not p.is_file():continue
 rel=p.resolve().relative_to(root).as_posix()
 q=subprocess.run(['git','check-ignore','-q','--',rel])
 assert q.returncode in [0,1],rel
 if q.returncode==0:ignored.append(rel);continue
 assert rel in objects,('File not in audited Git tree',rel);raw=subprocess.check_output(['git','cat-file','blob',objects[rel]]);h=hashlib.sha256(raw).hexdigest();assert h==sha(p),rel
 rows.append(dict(path=rel,git_blob=objects[rel],raw_sha256=h))
fixed(True)
if len(sys.argv)>1 and sys.argv[1]=='direct':
 assert not subprocess.check_output(['git','status','--porcelain'],encoding='utf-8').strip()
 branch=subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip();assert branch=='codex/research-online-linearization-migration'
 remote=subprocess.check_output(['git','ls-remote','origin','refs/heads/'+branch],encoding='utf-8').split()[0];assert remote==head
 pr=load(RUN/'created-PR-v1.json');current=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/'+str(pr['number'])]))
 assert current['head']['sha']==head and current['state']=='open' and current['draft'] and not current['merged']
 print(json.dumps(dict(status='DIRECT-no-file-write-passed',head=head,local_remote_REST_equal=True,clean=True,all_current_run_nonignored_raw_files_verified=len(rows),ignored_runtime_files_preserved=len(ignored),PR=current['html_url'],PRstate='OPEN-DRAFT-unmerged',goal_complete=False,chapter_complete=False,main_live_unchanged=True)))
else:
 write(RUN/'committed-raw-audit-v1.json',dict(status='passed-at-explicit-audited-head',audited_head=head,raw_files=len(rows),rows=rows,ignored_files_preserved=ignored,scope='Every current run nonignored file present before this audit creates its own record/wrapper files. Final DIRECT pass checks those later files too; no recursive self-head record.',all_raw_git_blobs_equal_current_bytes=True,source_package_accepted=load(RUN/'accepted-decision-v1.json')['source_package_accepted'],goal_complete=False))
 print('All',len(rows),'current run nonignored files exactly equal committed raw Git blobs; ignored runtime preserved.')
