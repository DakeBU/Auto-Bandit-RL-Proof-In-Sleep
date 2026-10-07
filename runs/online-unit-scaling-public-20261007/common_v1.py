"""Bounded current revalidation of existing unit-coordinate scaling."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,time
RUN=Path(__file__).resolve().parent;ROOT=RUN.parents[1];assert Path.cwd()==ROOT
BASE='f4f48c9c199248530a068677af536d673665c73d';TASK='ONLINE-UNIT-SCALING-PUBLIC-20261007'
BRANCH='codex/research-online-unit-scaling-migration';CONTRACT=Path('docs/contracts/online-unit-scaling-public-v1')
PUBLIC=Path('BanditRLProof/OnlineUnitScaling.lean');CANARY=Path('Tests/OnlineUnitScalingCanary.lean')
PRE='BanditRL.OnlineUnitScaling.';TEST='UnitScalingProbe.';ROUTE='online-unit-scaling'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,value):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(value if isinstance(value,bytes) else (value.rstrip('\n')+'\n' if isinstance(value,str) else json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):
 log=RUN/(label+'.log');receipt=RUN/(label+'-exit.json');assert not log.exists() and not receipt.exists();start=time.time()
 with log.open('wb') as stream:child=subprocess.run(list(map(str,args)),stdout=stream,stderr=subprocess.STDOUT)
 write(receipt,dict(command=list(map(str,args)),cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log)))
 print(label,'exit',child.returncode,flush=True)
 if child.returncode:raise RuntimeError(label+' failed; exact output preserved')
def native(label,*args):gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',*args)
def fixed(integrated=False):
 f=load(RUN/'draft-freeze-v1.json');allowed=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'] if integrated else []
 for p,h in f['fixed_files'].items():
  if p not in allowed:assert sha(p)==h,p
 sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
 for n,h in load(CONTRACT/'headers-v1.json').items():
  assert hashlib.sha256(h.encode()).hexdigest()==f['raw_headers'][n]
  assert hashlib.sha256(lean_declaration_header(PUBLIC,n).encode()).hexdigest()==f['native_headers'][n],n
 return f
