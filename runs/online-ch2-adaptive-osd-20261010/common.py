from pathlib import Path
import subprocess, json, hashlib, sys, time, base64

ROOT = Path(__file__).resolve().parents[2]
RUN = Path(__file__).resolve().parent
CONTRACT = ROOT/'docs/contracts/online-ch2-adaptive-osd-v1'
BASE = '0283616c8439b09fc49d5e35373ff74aa11371cc'
BRANCH = 'codex/research-online-ch2-adaptive-osd'
TASK = 'ONLINE-CH2-ADAPTIVE-OSD-20261010'
PDF = ROOT.parent/'research-online-ogd/tmp/pdfs/orabona-v10.pdf'
PDF_SHA = 'cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
PUBLIC = ROOT/'BanditRLProof/OnlineAdaptivePotential.lean'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
load = lambda p: json.loads(Path(p).read_text(encoding='utf8'))

def write(path, data):
    path = Path(path)
    assert not path.exists(), path
    path.parent.mkdir(parents=True, exist_ok=True)
    if isinstance(data, str):
        data = (data.rstrip('\n')+'\n').encode('utf8')
    elif not isinstance(data, bytes):
        data = (json.dumps(data, ensure_ascii=False, indent=2)+'\n').encode('utf8')
    path.write_bytes(data)

def rows(paths):
    return [dict(path=p.absolute().as_posix(), sha256=sha(p))
        for p in sorted(set(map(Path, paths))) if p.is_file()]

def capture(label, *args, required=True):
    assert Path.cwd() == ROOT
    start = time.monotonic()
    proc = subprocess.run(list(map(str, args)), cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    write(RUN/(label+'.json'), dict(command=list(map(str, args)), actual_exit=proc.returncode,
        cwd=ROOT.as_posix(), seconds=time.monotonic()-start,
        stdout_sha256=hashlib.sha256(proc.stdout).hexdigest(),
        stdout_base64=base64.b64encode(proc.stdout).decode('ascii')))
    out = proc.stdout.decode('utf8', errors='replace')
    print(label, 'actual exit', proc.returncode, flush=True)
    if required:
        assert proc.returncode == 0, (label, out)
    return proc.returncode, out

def event(label, kind, payload):
    return capture(label, sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
        'lifecycle-event', '--session', TASK, '--event', kind,
        '--payload-json', json.dumps(payload, separators=(',', ':')))
