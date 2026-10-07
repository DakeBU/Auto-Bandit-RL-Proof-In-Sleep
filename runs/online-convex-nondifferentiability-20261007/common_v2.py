from pathlib import Path
import hashlib,json,re,subprocess,sys
RUN=Path(__file__).resolve().parent;ROOT=RUN.parents[1]
assert Path('.').resolve()==ROOT
CONTRACT=Path('docs/contracts/online-convex-nondifferentiability-v1')
TASK='ONLINE-CONVEX-NONDIFFERENTIABILITY-20261007';PRE='BanditRL.OnlineConvex.'
BASE='57f96796d3bbbb42486a547cecce7d6b3da6e4ef';ROUTE='online-lipschitz'
PUBLIC=Path('BanditRLProof/OnlineConvexNondifferentiability.lean')
CANARY=Path('Tests/OnlineConvexNondifferentiabilityCanary.lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(x if isinstance(x,bytes) else (x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode())
def gate(label,*args):
 assert not (RUN/(label+'.log')).exists() and not (RUN/(label+'-exit.json')).exists()
 subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'run-command.py'),label,*map(str,args)],check=True)
def native(label,command,*args):gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',command,*args)
def passed(label):
 r=load(RUN/(label+'-exit.json'));assert r['exit_code']==0,label;return r
def event(stage,payload,attempt='v1'):
 native(stage+'-lifecycle-'+attempt,'lifecycle-event','--session',TASK,'--event',stage,'--payload-json',json.dumps({'run_id':RUN.name,'chapter_complete':False,'goal_complete':False,**payload}))
def fixed(integrated=False,body=False):
 f=load(RUN/'draft-freeze-v1.json')
 allowed=['BanditRLProof.lean','Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json'] if integrated else []
 for p,h in f['fixed_files'].items():
  if p not in allowed:assert sha(p)==h,p
 assert sha(CONTRACT/'complete-definition.lean')==f['complete_definition_sha256']
 if body:
  sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
  for n,h in f['headers'].items():assert hashlib.sha256(lean_declaration_header(PUBLIC,n).encode()).hexdigest()==h,n
 return f
def generated(name,paths):write(RUN/name,dict(before_first_use=True,rows=[dict(path=Path(p).as_posix(),sha256=sha(p)) for p in paths]))
