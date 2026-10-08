from pathlib import Path
import hashlib,json,subprocess,sys,time
RUN=Path(__file__).resolve().parent
ROOT=RUN.parents[1]
CONTRACT=ROOT/'docs/contracts/online-ftl-obstruction-v1'
TASK='ONLINE-FTL-OBSTRUCTION-20261009'
BRANCH='codex/research-online-ftl-obstruction'
BASE='224927197e78e1330c4c93e84f9c69388d3027a7'
PUBLIC=ROOT/'BanditRLProof/OnlineFTLOscillation.lean'
CANARY=ROOT/'Tests/OnlineFTLOscillationCanary.lean'
PDF=ROOT/'../research-online-ogd/tmp/pdfs/orabona-v10.pdf'
PDF_SHA='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf8'))
def write(p,value):
    p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
    if isinstance(value,str):value=(value.rstrip('\n')+'\n').encode('utf8')
    elif not isinstance(value,bytes):value=(json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode('utf8')
    p.write_bytes(value)
def gate(label,*args,required=True):
    assert Path.cwd()==ROOT
    log=RUN/(label+'.log');receipt=RUN/(label+'-exit.json')
    assert not log.exists() and not receipt.exists()
    tick=time.monotonic()
    with log.open('wb') as stream:child=subprocess.run(list(map(str,args)),cwd=str(ROOT),stdout=stream,stderr=subprocess.STDOUT)
    write(receipt,dict(command=list(map(str,args)),cwd=ROOT.as_posix(),actual_exit=child.returncode,seconds=time.monotonic()-tick,log_sha256=sha(log)))
    print(label,'actual exit',child.returncode,flush=True)
    if required:assert child.returncode==0,label
    return child.returncode
def native(label,*args):return gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',*args)
def rows(paths):return [dict(path=Path(p).resolve().as_posix(),sha256=sha(p)) for p in sorted(set(map(Path,paths)))]
def fixed():
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    for row in load(RUN/'baseline-v2.json')['rows']:assert sha(ROOT/row['path'])==row['sha256'],row['path']
