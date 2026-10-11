import datetime,hashlib,json,subprocess
from pathlib import Path
r=Path('E:/ABRL/worktrees/research-online-book');out=Path(__file__).parent
def capture(argv,name):
    p=subprocess.run(argv,cwd=r,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    for suffix,raw in [('stdout.raw',p.stdout),('stderr.raw',p.stderr)]:
        with (out/(name+'-'+suffix)).open('xb') as f:f.write(raw)
    return p
argv=['gh','run','list','--branch','codex/research-online-ch2-strong-convex-support','--limit','10','--json','databaseId,headSha,status,conclusion,workflowName,event,url']
p=capture(argv,'pr228-ci-snapshot-v1');assert p.returncode==0
rows=json.loads(p.stdout)
assert all(x['headSha']=='95cfc51fa11619217f8153614d5b5b8a6c04aa2d' for x in rows)
push=next(x for x in rows if x['databaseId']==38159854922)
assert push['event']=='push' and push['status']=='completed' and push['conclusion']=='failure'
log=capture(['gh','run','view','38159854922','--log-failed'],'pr228-push-failure-v1');assert log.returncode==0
assert b'CONTRIBUTOR_BASE: origin/main' in log.stdout and b'BanditRLProof/OnlineConstraintFiniteLoss.lean, BanditRLProof/OnlineConvexMinorant.lean' in log.stdout
record=dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_head='95cfc51fa11619217f8153614d5b5b8a6c04aa2d',actual_runs=rows,push_failure_verified=True,all_CI_green=False,main_live_updated=False,artifacts={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in out.glob('pr228-*v1-*.raw')})
with (out/'pr228-ci-observation-v1.json').open('x',encoding='utf-8') as f:json.dump(record,f,indent=2)
print(json.dumps({'recorded_runs':len(rows),'push_failure_verified':True,'all_CI_green':False}))
