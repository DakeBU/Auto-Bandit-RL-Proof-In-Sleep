"""Bounded current migration of the existing finite-history policy producer."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
RUN=Path(__file__).resolve().parent;ROOT=RUN.parents[1];assert Path('.').resolve()==ROOT
BASE='43598513e5bccb0e8e9ab3fe92ef43a22ee6638e';BASE_PR=179
TASK='ONLINE-OSD-POLICY-PUBLIC-20261007';ROUTE='online-osd-policy'
CONTRACT=Path('docs/contracts/online-osd-policy-public-v1')
PUBLIC=Path('BanditRLProof/OnlineSubgradientPolicy.lean');CANARY=Path('Tests/OnlineSubgradientPolicyCanary.lean')
PRE='BanditRL.OnlineSubgradientPolicy.'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(x if isinstance(x,bytes) else (x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'run-command.py'),label,*map(str,args)],check=True)
def native(label,command,*args):gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',command,*args)
def passed(label):
 r=load(RUN/(label+'-exit.json'));assert r['exit_code']==0,label;return r
def event(stage,payload,attempt='v1'):
 assert not any(k in payload for k in ['run_id','chapter_complete','goal_complete'])
 native(stage+'-lifecycle-'+attempt,'lifecycle-event','--session',TASK,'--event',stage,'--payload-json',json.dumps(dict(run_id=RUN.name,chapter_complete=False,goal_complete=False,**payload)))
def fixed(integrated=False):
 f=load(RUN/'draft-freeze-v1.json');allowed=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'] if integrated else []
 for p,h in f['fixed_files'].items():
  if p not in allowed:assert sha(p)==h,p
 sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
 text=PUBLIC.read_text(encoding='utf-8')
 for n,h in f['raw_headers'].items():
  m=re.search(r'(?m)^theorem '+re.escape(n)+r'\b[\s\S]*?(?= := by)',text);assert m,n
  raw=m.group(0).strip();assert hashlib.sha256(raw.encode()).hexdigest()==h
  normalized=lean_declaration_header(PUBLIC,n);assert ' '.join(raw.split())==normalized,n
  assert hashlib.sha256(normalized.encode()).hexdigest()==f['native_headers'][n],n
 return f
