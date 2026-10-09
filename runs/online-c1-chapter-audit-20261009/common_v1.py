from pathlib import Path
import subprocess,json,hashlib,time,sys
RUN=Path(__file__).resolve().parent
ROOT=RUN.parents[1]
CONTRACT=ROOT/'docs/contracts/online-c1-chapter-audit-v1'
BASE='a03f304522ed30ee34d43b38bd67deffbbf3b08f'
BRANCH='codex/research-online-c1-chapter-audit'
TASK='ONLINE-C1-CHAPTER-AUDIT-20261009'
PDF=(ROOT/'../research-online-ogd/tmp/pdfs/orabona-v10.pdf').resolve()
PDF_SHA='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf8'))
def write(p,v):
    p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
    if isinstance(v,str):v=(v.rstrip('\n')+'\n').encode('utf8')
    elif not isinstance(v,bytes):v=(json.dumps(v,ensure_ascii=False,indent=2)+'\n').encode('utf8')
    p.write_bytes(v)
def gate(label,*args,required=True):
    assert Path.cwd()==ROOT
    log=RUN/(label+'.log');out=RUN/(label+'-exit.json');assert not log.exists() and not out.exists()
    tick=time.monotonic()
    with log.open('wb') as stream:p=subprocess.run(list(map(str,args)),cwd=str(ROOT),stdout=stream,stderr=subprocess.STDOUT)
    write(out,dict(command=list(map(str,args)),cwd=ROOT.as_posix(),actual_exit=p.returncode,
        seconds=time.monotonic()-tick,log_sha256=sha(log)))
    print(label,'actual exit',p.returncode,flush=True)
    if required:assert p.returncode==0,label
    return p.returncode
def fixed():
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    for r in load(RUN/'baseline-v2.json')['rows']:assert sha(r['path'])==r['sha256'],r['path']
def rows(paths):return [dict(path=Path(p).resolve().as_posix(),sha256=sha(p)) for p in sorted(set(map(Path,paths)))]
