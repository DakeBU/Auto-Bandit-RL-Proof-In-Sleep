from common_integrated_v1 import *
fixed_integrated()
def read(args):
 r=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);assert r.returncode==0,args
 return r.stdout.decode('utf8').strip()
main=read(['git','-C','E:/ABRL/research','rev-parse','HEAD']);origin=read(['git','rev-parse','origin/main']);canonical_status=read(['git','-C','E:/ABRL/research','status','--porcelain','--untracked-files=all'])
assert main==origin=='6847b678a73db68dee5101d6f05c2453c1405afc' and not canonical_status
pr=json.loads(read(['gh','pr','view','191','--json','state,isDraft,mergedAt,headRefOid,baseRefName,headRefName,url']))
assert pr['state']=='OPEN' and pr['isDraft'] and pr['mergedAt'] is None and pr['headRefOid']==BASE and pr['headRefName']==BASE_BRANCH
write(RUN/'current-state-v1.json',dict(canonical_main=main,origin_main=origin,canonical_clean=True,actual_base_PR=pr,active_branch=read(['git','branch','--show-current']),head=read(['git','rev-parse','HEAD']),shared_git_common=read(['git','rev-parse','--git-common-dir']),worktrees=read(['git','worktree','list','--porcelain']),globalSGB_sha256=sha('runs/active_frontier.json'),no_shared_links_or_retirement_mutation=True,chapter_complete=False,goal_complete=False,merged=False,live=False))
cmd=[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main'];log=RUN/'main-relative-diagnostic-v1.log';start=time.time()
with log.open('wb') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
write(RUN/'main-relative-diagnostic-v1-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=r.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log),scope='Diagnostic of remaining full stacked-main contribution coverage; an expected failed diagnostic is never an accepted gate or waiver. Exact-base gate separately required.',chapter_complete=False,goal_complete=False))
print('Canonical/main/basePR exact and retained. Main-relative diagnostic actual exit',r.returncode)
print(log.read_text(encoding='utf8')[-2200:])
fixed_integrated()
