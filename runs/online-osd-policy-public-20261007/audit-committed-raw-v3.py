"""Strict explicit-head/full-tree Git raw-byte audit; original failure preserved."""
from common_v1 import *
fixed(True)
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()
command=['git','ls-tree','-r','-z','--full-tree',head,'--',RUN.relative_to(ROOT).as_posix()]
raw_tree=subprocess.check_output(command);objects={e.split(bytes([9]),1)[1].decode('utf-8'):e.split(bytes([9]),1)[0].split()[2].decode('ascii') for e in raw_tree.split(bytes([0])) if e}
assert objects;rows=[];ignored=[]
for p in sorted(RUN.rglob('*')):
 if not p.is_file():continue
 rel=p.resolve().relative_to(ROOT).as_posix();q=subprocess.run(['git','check-ignore','-q','--',rel]);assert q.returncode in [0,1],rel
 if q.returncode==0:ignored.append(rel);continue
 assert rel in objects,dict(path=rel,audited_head=head,full_tree_paths=len(objects))
 blob=subprocess.check_output(['git','cat-file','blob',objects[rel]]);h=hashlib.sha256(blob).hexdigest();assert h==sha(p),rel
 rows.append(dict(path=rel,git_blob=objects[rel],raw_sha256=h))
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()==head
if len(sys.argv)>1 and sys.argv[1]=='direct':
 assert not subprocess.check_output(['git','status','--porcelain'],encoding='utf-8').strip()
 branch=subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip();assert branch=='codex/research-online-osd-policy-migration'
 remote=subprocess.check_output(['git','ls-remote','origin','refs/heads/'+branch],encoding='utf-8').split()[0];assert remote==head
 pr=load(RUN/'created-PR-v1.json');current=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/'+str(pr['number'])]))
 assert current['head']['sha']==head and current['state']=='open' and current['draft'] and not current['merged']
 print(json.dumps(dict(status='DIRECT-no-file-write-passed',head=head,local_remote_REST_equal=True,clean=True,all_current_run_nonignored_raw_files_verified=len(rows),ignored_runtime_files_preserved=len(ignored),PR=current['html_url'],PRstate='OPEN-DRAFT-unmerged',goal_complete=False,chapter_complete=False,main_live_unchanged=True)))
else:
 write(RUN/'committed-raw-tree-v3.bin',raw_tree)
 write(RUN/'committed-raw-audit-v3.json',dict(status='passed-at-explicit-audited-head',audited_head=head,actual_command=command,tree_files=len(objects),raw_tree_sha256=sha(RUN/'committed-raw-tree-v3.bin'),raw_files=len(rows),rows=rows,ignored_files_preserved=ignored,scope='Every nonignored current RUN file existing before this audit creates raw-tree/report/wrapper files. Final DIRECT checks every later file too; no self-head artifact.',all_raw_git_blobs_equal_current_bytes=True,source_package_accepted=load(RUN/'accepted-decision-v1.json')['source_package_accepted'],preserved_actual_failure='committed-raw-audit-v1-01',initial_failure_mechanism_unresolved=True,chapter_complete=False,goal_complete=False))
 print('All',len(rows),'current RUN raw files match explicit-head full-tree Git blobs; separate delivery metadata review pending.')
