from pathlib import Path
import hashlib,json,re,subprocess,sys,time
RUN=Path(__file__).resolve().parent;ROOT=RUN.parents[1]
assert Path.cwd()==ROOT
BASE='0fc48df995bc9c65046e78722a4f436033fe5554'
BASE_PR=187;BASE_BRANCH='codex/research-online-foundations-migration'
BRANCH='codex/research-online-ftl-sharp';TASK='ONLINE-FTL-SHARP-20261007'
CONTRACT=Path('docs/contracts/online-ftl-sharp-v1')
PUBLIC=Path('BanditRLProof/OnlineLearningFTL.lean')
CANARY=Path('Tests/OnlineLearningFTLSharpCanary.lean')
PRE='BanditRL.OnlineLearning.';TEST='FTLSharpProbe.';ROUTE='online-foundations'
PDF=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
PDF_SHA='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,value):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(value if isinstance(value,bytes) else (value.rstrip('\n')+'\n' if isinstance(value,str) else json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):
 log=RUN/(label+'.log');record=RUN/(label+'-exit.json');assert not log.exists() and not record.exists()
 start=time.time()
 with log.open('wb') as stream:child=subprocess.run(list(map(str,args)),stdout=stream,stderr=subprocess.STDOUT)
 write(record,dict(command=list(map(str,args)),cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log)))
 print(label,'exit',child.returncode,flush=True)
 if child.returncode:raise RuntimeError(label+' failed; raw evidence retained')
def native(label,*args):gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',*args)
def fixed(proving=False,integrated=False):
 f=load(RUN/'draft-freeze-v1.json')
 for p,h in f['fixed_files'].items():
  if proving and p==PUBLIC.as_posix():continue
  if integrated and p in ['Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:continue
  assert sha(p)==h,p
 if proving:
  old=(RUN/'snapshots/BanditRLProof--OnlineLearningFTL.lean.raw').read_bytes()
  end=b'end BanditRL.OnlineLearning\r\n' if old.endswith(b'\r\n') else b'end BanditRL.OnlineLearning\n'
  assert old.endswith(end)
  assert PUBLIC.read_bytes().startswith(old[:-len(end)]),'All existing public text must be exact original prefix'
 if integrated:assert Path('Tests.lean').read_bytes()==(RUN/'snapshots/Tests.lean.raw').read_bytes()+b'\nimport Tests.OnlineLearningFTLSharpCanary\n'
 assert sha(PDF)==PDF_SHA
 return f
