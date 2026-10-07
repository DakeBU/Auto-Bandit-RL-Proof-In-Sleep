from pathlib import Path
import hashlib,json,re,subprocess,sys,time
RUN=Path(__file__).resolve().parent; ROOT=RUN.parents[1]
assert Path.cwd()==ROOT
BASE='e2323f4ca649a30e420bde1a33dbf1d4997c4c9b'
BASE_BRANCH='codex/research-online-ftl-sharp'; BASE_PR=188
BRANCH='codex/research-online-ftl-state'; TASK='ONLINE-FTL-STATE-20261007'
CONTRACT=Path('docs/contracts/online-ftl-state-v1')
MEAN=Path('BanditRLProof/OnlineLearningMean.lean')
PUBLIC=Path('BanditRLProof/OnlineLearningFTLState.lean')
CANARY=Path('Tests/OnlineLearningFTLStateCanary.lean')
PRE='BanditRL.OnlineLearning.'; TEST='FTLStateProbe.'
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
 with log.open('wb') as stream:p=subprocess.run(list(map(str,args)),stdout=stream,stderr=subprocess.STDOUT)
 write(record,dict(command=list(map(str,args)),cwd=ROOT.as_posix(),exit_code=p.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log)))
 print(label,'exit',p.returncode,flush=True)
 if p.returncode:raise RuntimeError(label+' failed; original evidence retained')
def native(label,*args):gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',*args)
def fixed(proving=False,integrated=False):
 f=load(RUN/'draft-freeze-v1.json')
 for p,h in f['fixed_files'].items():
  if proving and p==MEAN.as_posix():continue
  if integrated and p in ['BanditRLProof.lean','Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:continue
  assert sha(p)==h,p
 if proving:
  old=(RUN/'snapshots/BanditRLProof--OnlineLearningMean.lean.raw').read_bytes()
  end=b'end BanditRL.OnlineLearning\r\n' if old.endswith(b'\r\n') else b'end BanditRL.OnlineLearning\n'
  assert old.endswith(end) and MEAN.read_bytes().startswith(old[:-len(end)]),'Old Mean definitions and four proof bodies exact'
 assert sha(PDF)==PDF_SHA
 return f
