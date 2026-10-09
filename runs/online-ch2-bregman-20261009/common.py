from pathlib import Path
import subprocess,json,hashlib,sys,time,base64
ROOT=Path(__file__).resolve().parents[2]
RUN=Path(__file__).resolve().parent
CONTRACT=ROOT/'docs/contracts/online-ch2-bregman-v1'
BASE='71f2219fa1648094eba8aa17b50e443258f436cb'
BRANCH='codex/research-online-ch2-bregman'
TASK='ONLINE-CH2-BREGMAN-20261009'
PUBLIC=ROOT/'BanditRLProof/OnlineBregmanProximal.lean'
PDF=ROOT.parent/'research-online-ogd/tmp/pdfs/orabona-v10.pdf'
PDF_SHA='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf8'))
def write(p,data):
    p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
    if isinstance(data,str):data=(data.rstrip('\n')+'\n').encode('utf8')
    elif not isinstance(data,bytes):data=(json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8')
    p.write_bytes(data)
def rows(paths):
    return [dict(path=p.absolute().as_posix(),sha256=sha(p)) for p in sorted(set(map(Path,paths))) if p.is_file()]
def capture(label,*args,required=True):
    assert Path.cwd()==ROOT
    start=time.monotonic();p=subprocess.run(list(map(str,args)),cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    write(RUN/(label+'.json'),dict(command=list(map(str,args)),actual_exit=p.returncode,cwd=ROOT.as_posix(),seconds=time.monotonic()-start,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii')))
    print(label,'actual exit',p.returncode,flush=True)
    if required:assert p.returncode==0,(label,p.stdout.decode('utf8',errors='replace'))
    return p.returncode,p.stdout.decode('utf8',errors='replace')
def fixed():
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    if (RUN/'baseline-v1.json').exists():
        for row in load(RUN/'baseline-v1.json')['rows']:assert sha(row['path'])==row['sha256'],row['path']
def event(label,kind,payload):
    return capture(label,sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','lifecycle-event','--session',TASK,'--event',kind,'--payload-json',json.dumps(payload,separators=(',',':')))
