from pathlib import Path
import hashlib,json,subprocess,sys,time,re
RUN=Path(__file__).resolve().parent;ROOT=RUN.parents[1]
assert Path.cwd()==ROOT
BASE='9425fecb38be60b1acb7a918cb149f72117133ad';BASE_PR=190;BASE_BRANCH='codex/research-online-regret-domains'
BRANCH='codex/research-online-log-lower';TASK='ONLINE-GUESSING-LOG-LOWER-20261008'
CONTRACT=Path('docs/contracts/online-guessing-log-lower-v1')
PUBLIC=Path('BanditRLProof/OnlineGuessingLogLower.lean');CANARY=Path('Tests/OnlineGuessingLogLowerCanary.lean')
PRE='BanditRL.OnlineLearning.GuessingLower.'
PDF=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');PDF_SHA='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,value):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(value if isinstance(value,bytes) else (value.rstrip('\n')+'\n' if isinstance(value,str) else json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):
 log=RUN/(label+'.log');out=RUN/(label+'-exit.json');assert not log.exists() and not out.exists();start=time.time()
 with log.open('wb') as stream:r=subprocess.run(list(map(str,args)),stdout=stream,stderr=subprocess.STDOUT)
 write(out,dict(command=list(map(str,args)),cwd=ROOT.as_posix(),exit_code=r.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log)))
 print(label,'exit',r.returncode,flush=True)
 if r.returncode:raise RuntimeError(label+' failed; exact failure retained')
def native(label,*args):gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',*args)
def fixed():
 assert sha(PDF)==PDF_SHA
 for p,h in load(RUN/'draft-freeze-v1.json')['fixed_files'].items():assert sha(p)==h,p
