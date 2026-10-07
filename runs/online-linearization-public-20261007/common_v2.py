"""Bounded revalidation of the preexisting causal convex-to-linear reduction."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,time
RUN=Path(__file__).resolve().parent;ROOT=RUN.parents[1];assert Path.cwd()==ROOT
BASE='1b513c60fc9ba5ff8db18a75a95deca59f5cbd85';TASK='ONLINE-LINEARIZATION-PUBLIC-20261007'
BRANCH='codex/research-online-linearization-migration';CONTRACT=Path('docs/contracts/online-linearization-public-v1')
PUBLIC=Path('BanditRLProof/OnlineLinearization.lean');CANARY=Path('Tests/OnlineLinearizationCanary.lean')
PRE='BanditRL.OnlineLinearization.';TEST='LinearizationProbe.';ROUTE='online-linearization'
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
 f=load(RUN/'draft-freeze-v2.json');allowed=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'] if integrated else []
 for p,h in f['fixed_files'].items():
  if p not in allowed:assert sha(p)==h,p
 sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
 for n,h in load(CONTRACT/'headers-v2.json').items():
  assert hashlib.sha256(h.encode()).hexdigest()==f['raw_headers'][n]
  assert hashlib.sha256(lean_declaration_header(PUBLIC,n).encode()).hexdigest()==f['native_headers'][n],n
 return f
