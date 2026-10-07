"""Bounded current Lemma 1.2 reuse and named, nondegenerate canaries."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,time
RUN=Path(__file__).resolve().parent; ROOT=RUN.parents[1]
assert Path.cwd()==ROOT
BASE='881a1f57a2a018b16418e8ea62b869be5861d33e'
BASE_PR=186; BASE_BRANCH='codex/research-online-unit-scaling-migration'
BRANCH='codex/research-online-foundations-migration'
TASK='ONLINE-FOUNDATIONS-PUBLIC-20261007'
CONTRACT=Path('docs/contracts/online-foundations-public-v1')
PUBLIC=Path('BanditRLProof/OnlineLearningFoundations.lean')
CANARY=Path('Tests/OnlineLearningFoundationsCanary.lean')
PRE='BanditRL.OnlineLearning.'; TEST='FoundationsProbe.'; ROUTE='online-foundations'
PDF=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
PDF_SHA='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,value):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(value if isinstance(value,bytes) else (value.rstrip('\n')+'\n' if isinstance(value,str) else json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):
 log=RUN/(label+'.log');receipt=RUN/(label+'-exit.json');assert not log.exists() and not receipt.exists()
 start=time.time()
 with log.open('wb') as stream: child=subprocess.run(list(map(str,args)),stdout=stream,stderr=subprocess.STDOUT)
 write(receipt,dict(command=list(map(str,args)),cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log)))
 print(label,'exit',child.returncode,flush=True)
 if child.returncode:raise RuntimeError(label+' failed; original evidence retained')
def native(label,*args):gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',*args)
def fixed(integrated=False):
 f=load(RUN/'draft-freeze-v1.json')
 for p,h in f['fixed_files'].items():
  if integrated and p in ['Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:continue
  assert sha(p)==h,p
 if integrated:
  old=(RUN/'snapshots/Tests.lean.raw').read_bytes()
  assert Path('Tests.lean').read_bytes()==old+b'\nimport Tests.OnlineLearningFoundationsCanary\n'
 sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
 assert hashlib.sha256(lean_declaration_header(PUBLIC,'lemma_1_2').encode()).hexdigest()==f['native_header_hash']
 assert sha(PDF)==PDF_SHA
 return f
