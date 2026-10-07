from pathlib import Path
import hashlib,json,re,subprocess,sys,time
RUN=Path(__file__).resolve().parent; ROOT=RUN.parents[1]
assert Path.cwd()==ROOT
BASE='8ce8cc580bd7311482dd40234aaf34bd9a909a8b'
TASK='ONLINE-GUESSING-OSD-POLICY-20261007'
CONTRACT=Path('docs/contracts/online-guessing-osd-policy-v1')
PUBLIC=Path('BanditRLProof/OnlineGuessingSubgradientPolicy.lean')
CANARY=Path('Tests/OnlineGuessingSubgradientPolicyCanary.lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,value):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 raw=value if isinstance(value,bytes) else (value.rstrip('\n')+'\n' if isinstance(value,str) else json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode('utf-8')
 p.write_bytes(raw)
def gate(label,*args):
 log=RUN/(label+'.log');receipt=RUN/(label+'-exit.json');assert not log.exists() and not receipt.exists()
 start=time.time()
 with log.open('wb') as stream: result=subprocess.run(list(map(str,args)),stdout=stream,stderr=subprocess.STDOUT)
 write(receipt,dict(command=list(map(str,args)),cwd=ROOT.as_posix(),exit_code=result.returncode,seconds=round(time.time()-start,3),log=log.as_posix(),log_sha256=sha(log)))
 print(label,'exit',result.returncode,flush=True)
 if result.returncode:raise RuntimeError(label+' failed; exact raw log retained')
def native(label,*args):gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',*args)
def fixed():
 for path,h in load(RUN/'draft-freeze-v1.json')['fixed_files'].items():assert sha(path)==h,path
def headers():
 if PUBLIC.exists():
  actual={m.group(1):m.group(0).strip() for m in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?(?= := by)',PUBLIC.read_text(encoding='utf-8'))}
  assert actual==load(CONTRACT/'headers-v1.json'),actual
 fixed()
