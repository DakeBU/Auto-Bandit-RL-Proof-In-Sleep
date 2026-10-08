from pathlib import Path
import gzip, hashlib, json, subprocess, sys, time

RUN=Path(__file__).resolve().parent
ROOT=RUN.parents[1]
BASE='6b387a39e401cb1b90003fca6e49d3bdd9ce7a9a'
BRANCH='codex/research-online-c1-core-audit'
TASK='ONLINE-C1-CORE-AUDIT-20261008'
CONTRACT=Path('docs/contracts/online-c1-core-audit-v1')
CANARY=Path('Tests/OnlineLearningCoreAuditCanary.lean')
PDF=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
PDF_SHA='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
PRE='BanditRL.OnlineLearning.'
MODULES=[Path('BanditRLProof')/(name+'.lean') for name in ['OnlineLearningFoundations','OnlineLearningStochastic','OnlineLearningInformation','OnlineLearningIID','OnlineLearningHistory']]
sha=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p: json.loads(Path(p).read_text(encoding='utf8'))

def write(p,value):
    p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes(value if isinstance(value,bytes) else (value.rstrip('\n')+'\n' if isinstance(value,str) else json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode('utf8'))

def gate(label,*args,require=True):
    log=RUN/(label+'.log');receipt=RUN/(label+'-exit.json')
    assert not log.exists() and not receipt.exists()
    tick=time.monotonic()
    with log.open('wb') as stream: child=subprocess.run(list(map(str,args)),stdout=stream,stderr=subprocess.STDOUT)
    write(receipt,dict(command=list(map(str,args)),cwd=ROOT.as_posix(),exit_code=child.returncode,
        seconds=time.monotonic()-tick,log_sha256=sha(log)))
    print(label,'actual exit',child.returncode,flush=True)
    if require: assert child.returncode==0,label
    return child.returncode

def native(label,*args): return gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',*args)

def fixed():
    assert Path.cwd()==ROOT
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    assert sha(PDF)==PDF_SHA
    for p,h in load(RUN/'draft-baseline-v1.json')['fixed_files'].items(): assert sha(p)==h,p
