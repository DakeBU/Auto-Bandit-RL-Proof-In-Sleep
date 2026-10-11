from pathlib import Path
import subprocess,hashlib,json,datetime
R=Path('E:/ABRL/worktrees/research-online-book'); D=R/'tmp/online-main-reconciliation-20261011'
OLD='c445c93f7e4cda1408279d614858c904e346ad47'; MAIN='f07aa9a2a5df241087ffab1c3579d1b59d8bf6f6'
BRANCH='codex/research-online-ch2-strong-convex-growth'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_bytes())
def need(b,s):
    if not b:raise ValueError(s)
def capture(label,argv,exits=(0,)):
    out=D/'actual-merge'/label;need(not out.exists(),'create-only command evidence');out.mkdir(parents=True)
    start=datetime.datetime.now(datetime.timezone.utc).isoformat();p=subprocess.run(argv,cwd=R,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    (out/'stdout.raw').write_bytes(p.stdout);(out/'stderr.raw').write_bytes(p.stderr)
    (out/'receipt.json').write_bytes((json.dumps({'argv':argv,'actual_exit':p.returncode,'start_utc':start,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n').encode())
    need(p.returncode in exits,label+' failed');return p
need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=R).decode().strip()==OLD,'HEAD')
need(not subprocess.check_output(['git','status','--porcelain=v1','-z'],cwd=R),'clean start')
need(sha(D/'parent-code-readiness-v2.json')=='25eca7ab1287c2ae9b02180f4daa1e820957f514ee3474f741d802aedeb86066','parent plan')
need(sha(D/'independent-prepared-review-v2.json')=='7cd6fa19b286a1a3e508a61bc5f9bcab0129d8d501599a4c38a51314b8989afc','independent plan')
need(not load(D/'independent-prepared-review-v2.json')['blockers'],'prepared blockers')
code=load(D/'parent-code-readiness-v2.json')['candidate_files']; book=load(D/'book-plan-v1/reconciliation-plan-v1.json')
need(sha(D/'book-plan-v1/reconciliation-plan-v1.json')=='0f337d3927566c9e04fcfd6a544b16dd2cbeaf823f4ebd4a9aa4ab8e1f619060','book plan')
rows=list(code)
for name,h in book['candidate_sha256'].items():
    p=D/'book-plan-v1/candidate'/(name+'.json');rows.append({'path':'website/content/'+name+'.json','suggested_path':str(p.relative_to(R)),'sha256':h,'bytes':p.stat().st_size})
need(len(rows)==11 and len({x['path'] for x in rows})==11,'exact 11 files')
for row in rows:need(sha(R/row['suggested_path'])==row['sha256'],'candidate '+row['path'])
capture('switch',['git','switch','-c',BRANCH])
capture('merge',['git','merge','--no-commit','--no-ff',MAIN],(1,))
conflicts=subprocess.check_output(['git','diff','--name-only','--diff-filter=U','-z'],cwd=R).decode().strip('\0').split('\0')
need(set(conflicts)=={x['path'] for x in rows if x['path']!='website/scripts/check_site.py'},'conflict set changed')
for row in rows:
    b=(R/row['suggested_path']).read_bytes();(R/row['path']).write_bytes(b);need(sha(R/row['path'])==row['sha256'],'applied bytes')
capture('resolve',['git','add','--',*[x['path'] for x in rows]])
need(not subprocess.check_output(['git','ls-files','-u'],cwd=R),'unresolved entries')
need(sha(R/'docs/contracts/online-ch2-complete-target-freeze-v1/effective-targets-frozen-v3.2.json')=='61cf1901a632aeee35ee71511ba53b115ae0958649ea78b786536a4404684ba1','inventory changed')
rec={'status':'reviewed merge candidate applied and staged; not committed, tested or accepted','parents':[OLD,MAIN],'branch':BRANCH,'candidates':rows,'resolved_conflicts':conflicts,'HEAD_still':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R).decode().strip(),'strongconvex_BODY':False,'strongconvex_frozen':False,'required_next':'Durably retain archive inputs and predecessor delivery; add honest contribution manifest; stabilize candidate commit, then fresh combined gates/site/reader/source-line successor audits.'}
p=D/'actual-merge/application-v1.json';need(not p.exists(),'application create-only');p.write_bytes((json.dumps(rec,indent=2)+'\n').encode());print(json.dumps({'application':str(p),'sha256':sha(p),'resolved':len(conflicts),'candidate_files':len(rows)}))
