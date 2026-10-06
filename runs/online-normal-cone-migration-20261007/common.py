from pathlib import Path
import hashlib,json,re,subprocess,sys
RUN=Path(__file__).resolve().parent;ROOT=RUN.parents[1]
assert Path('.').resolve()==ROOT,'Every actual edit/build command must use the active worktree cwd'
CONTRACT=Path('docs/contracts/online-normal-cone-migration-v1');TASK='ONLINE-NORMAL-CONE-MIGRATION-20261007';ROUTE='online-normal-cone';PRE='BanditRL.OnlineConvex.'
PUBLIC=Path('BanditRLProof/OnlineNormalCone.lean');CANARY=Path('Tests/OnlineNormalConeCanary.lean');BASE='9cb6dc7f111f2d1c4925cfbfb3d29b9410f2bc0d'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(x if isinstance(x,bytes) else (x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode())
def gate(label,*args):
 assert not (RUN/(label+'.log')).exists() and not (RUN/(label+'-exit.json')).exists(),('Immutable evidence label, choose a new version',label)
 subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'run-command.py'),label,*map(str,args)],check=True)
def native(label,command,*args):gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',command,*args)
def passed(label):
 r=load(RUN/(label+'-exit.json'));assert r['exit_code']==0,label;return r

def event(stage,payload,attempt='v1'):
 native(stage+'-lifecycle-'+attempt,'lifecycle-event','--session',TASK,'--event',stage,'--payload-json',json.dumps(dict(run_id=RUN.name,chapter_complete=False,goal_complete=False,**payload)))
def fixed(qualified=False):
 f=load(RUN/'draft-freeze-v1.json');row=next(r for r in load(RUN/'historical-raw-supersession-v2.json')['rows'] if r['path']==PUBLIC.as_posix())
 if qualified:assert PUBLIC.read_bytes().endswith(Path(row['snapshot']).read_bytes())
 else:assert sha(PUBLIC)==f['original_module_sha256']
 for k in ['whole_old_canary','fixed_shared_files']:
  for p,h in f[k].items():assert sha(p)==h,p
 sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
 for n,h in f['headers'].items():assert hashlib.sha256(lean_declaration_header(PUBLIC,n).encode()).hexdigest()==h,n
 return f

def generated(label,paths):write(RUN/label,dict(before_first_use=True,rows=[dict(path=Path(p).as_posix(),sha256=sha(p)) for p in paths]))
def inputs(name,extra=()):
 paths={p.as_posix() for directory in [RUN,CONTRACT] for p in directory.rglob('*') if p.is_file() and '__pycache__' not in p.parts};paths.update(extra)
 write(RUN/name,dict(ignored_runtime_excluded=True,source_package_accepted=False,chapter_complete=False,goal_complete=False,rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
def bind_review(receipt,manifest,out):
 r=load(RUN/receipt);assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
 assert sha(r['report'])==r['report_sha256']
 for key in ['required_repairs','required_mathematical_repairs','mathematical_repairs']:assert not r.get(key,[]),(key,r.get(key))
 reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
 for row in load(RUN/manifest)['rows']:assert reviewed[row['path']]==row['sha256']==sha(row['path']),row['path']
 for p,h in reviewed.items():assert sha(p)==h,p
 write(RUN/out,dict(status='passed-at-review-boundary',reviewed_raw_paths=len(reviewed),report_sha256=r['report_sha256'],required_reader_corrections=r.get('required_reader_corrections',[]),mathematical_repairs=[]))
 return r
