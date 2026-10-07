"""Bound this existing public producer-chain audit, with distinct raw/native hashes."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
RUN=Path(__file__).resolve().parent;ROOT=RUN.parents[1];assert Path('.').resolve()==ROOT
CONTRACT=Path('docs/contracts/online-osd-public-v1');TASK='ONLINE-OSD-PUBLIC-20261007'
BASE='2ee95f4c340266847ae577a8e018f5bbf55451b9';ROUTE='online-osd';PRE='BanditRL.OnlineSubgradientDescent.'
PUBLIC=Path('BanditRLProof/OnlineSubgradientDescent.lean');CANARY=Path('Tests/OnlineSubgradientDescentCanary.lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(x if isinstance(x,bytes) else (x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'run-command.py'),label,*map(str,args)],check=True)
def native(label,command,*args):gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',command,*args)
def passed(label):
 r=load(RUN/(label+'-exit.json'));assert r['exit_code']==0,label;return r
def event(stage,payload,attempt='v1'):native(stage+'-lifecycle-'+attempt,'lifecycle-event','--session',TASK,'--event',stage,'--payload-json',json.dumps(dict(run_id=RUN.name,chapter_complete=False,goal_complete=False,**payload)))
def fixed(integrated=False):
 f=load(RUN/'draft-freeze-v1.json');allowed=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'] if integrated else []
 for p,h in f['fixed_files'].items():
  if p not in allowed:assert sha(p)==h,p
 sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
 text=PUBLIC.read_text(encoding='utf-8')
 for n,h in f['raw_headers'].items():
  m=re.search(r'(?m)^theorem '+re.escape(n)+r'\b[\s\S]*?(?= :=)',text);assert m,n
  assert hashlib.sha256(m.group(0).strip().encode()).hexdigest()==h,('raw',n)
  assert hashlib.sha256(lean_declaration_header(PUBLIC,n).encode()).hexdigest()==f['native_headers'][n],('native',n)
 return f
