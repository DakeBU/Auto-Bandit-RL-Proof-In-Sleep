import datetime,hashlib,json,subprocess
from pathlib import Path
r=Path('E:/ABRL/worktrees/research-online-book')
def run(argv):return subprocess.check_output(argv,cwd=r)
pr=json.loads(run(['gh','pr','view','228','--json','number,url,state,isDraft,baseRefName,baseRefOid,headRefName,headRefOid']))
assert pr['state']=='OPEN' and pr['isDraft'] is True
assert pr['headRefOid']=='95cfc51fa11619217f8153614d5b5b8a6c04aa2d'
assert pr['baseRefOid']=='20d223bb3f45a51e746310e74759ed2e89dd7944'
remote=run(['git','-c','core.longpaths=true','ls-remote','origin','refs/heads/codex/research-online-ch2-strong-convex-support']).decode().strip()
assert remote.split()[0]==pr['headRefOid']
status=run(['git','-c','core.longpaths=true','status','--porcelain=v1','-z']).hex()
assert not status
body=r/'tmp/online-support-resume-20261012/support-pr-body-v1.md'
record=dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),pr=pr,remote=remote,git_status_hex=status,body_file_sha256=hashlib.sha256(body.read_bytes()).hexdigest(),artifact_attached=True,canonical_source='E:/ABRL/research',worktree=str(r),main_updated=False,live_updated=False,reader_capture_in_progress='actual-render-v3',native_status='Registration-time pending native retained; no final closure upgrade claimed.',known_unresolved='Six inherited origin/main provenance row occurrences; push CI can fail. Full iff/support existence/vector adapter production/attainment/cumulative guarantees/chapter closure remain open.',global_goal='ACTIVE',temporary_worktree='retained for active proof and gate work')
with (Path(__file__).parent/'pr228-delivery-observation-v1.json').open('x',encoding='utf-8') as f:json.dump(record,f,indent=2)
print(json.dumps({'pr':pr['url'],'verified_remote_head':pr['headRefOid'],'clean':True}))
