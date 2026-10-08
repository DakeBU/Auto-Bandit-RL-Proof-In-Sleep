from pathlib import Path
import hashlib,json,subprocess,sys,time
RUN=Path(__file__).resolve().parent;ROOT=RUN.parents[1]
assert Path.cwd()==ROOT
BASE='2aa08b9e1f5da4d0c7d7dcbe9ddeadd1fbfc34e3';BASE_BRANCH='codex/research-online-no-regret';BASE_PR=192
BRANCH='codex/research-online-benchmarks';TASK='ONLINE-SQUARE-MINIMUM-20261008'
CONTRACT=Path('docs/contracts/online-square-minimum-v1')
PUBLIC=Path('BanditRLProof/OnlineSquareMinimum.lean');CANARY=Path('Tests/OnlineSquareMinimumCanary.lean')
PDF=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');PDF_SHA='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf8'))
def write(p,v):
    p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes(v if isinstance(v,bytes) else (v.rstrip('\n')+'\n' if isinstance(v,str) else json.dumps(v,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
def gate(label,*args):
    log=RUN/(label+'.log');receipt=RUN/(label+'-exit.json');assert not log.exists() and not receipt.exists();start=time.time()
    with log.open('wb') as f:r=subprocess.run([str(a) for a in args],stdout=f,stderr=subprocess.STDOUT)
    write(receipt,dict(command=list(map(str,args)),cwd=ROOT.as_posix(),exit_code=r.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log)))
    print(label,'exit',r.returncode,flush=True)
    if r.returncode:raise RuntimeError(label+' failed; raw failure retained')
def native(label,*args):gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',*args)
def fixed():
    assert sha(PDF)==PDF_SHA
    for p,h in load(RUN/'draft-baseline-v1.json')['fixed_files'].items():assert sha(p)==h,p
