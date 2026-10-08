from pathlib import Path
import hashlib, json, subprocess, sys, time

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[1]
TASK = 'ONLINE-AE-CAUSAL-20261008'
BRANCH = 'codex/research-online-ae-causal'
BASE = '4ca57025a2cdc4f4ba0d5cc2423b55786b0a7afe'
CONTRACT = ROOT / 'docs/contracts/online-ae-causal-v1'
PUBLIC = ROOT / 'BanditRLProof/OnlineGuessingAECausal.lean'
PDF = ROOT / '../research-online-ogd/tmp/pdfs/orabona-v10.pdf'
PDF_SHA = 'cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
load = lambda p: json.loads(Path(p).read_text(encoding='utf8'))

def write(p, value):
    p = Path(p)
    assert not p.exists(), p
    p.parent.mkdir(parents=True, exist_ok=True)
    content = value if isinstance(value, bytes) else (
        value.rstrip('\n') + '\n' if isinstance(value, str)
        else json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf8')
    p.write_bytes(content)

def gate(label, *args, required=True):
    log, receipt = RUN / (label + '.log'), RUN / (label + '-exit.json')
    assert not log.exists() and not receipt.exists()
    start = time.monotonic()
    with log.open('wb') as stream:
        child = subprocess.run(list(map(str, args)), stdout=stream, stderr=subprocess.STDOUT)
    write(receipt, dict(command=list(map(str, args)), cwd=ROOT.as_posix(),
        actual_exit=child.returncode, seconds=time.monotonic()-start, log_sha256=sha(log)))
    print(label, 'actual exit', child.returncode, flush=True)
    if required:
        assert child.returncode == 0, label
    return child.returncode

def native(label, *args):
    return gate(label, sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', *args)

def baseline_fixed(mutable=()):
    assert Path.cwd() == ROOT
    assert subprocess.check_output(['git','branch','--show-current'], encoding='utf8').strip() == BRANCH
    assert sha(PDF) == PDF_SHA
    for row in load(RUN/'draft-baseline-v1.json')['rows']:
        assert sha(ROOT/row['snapshot']) == row['sha256']
        if row['path'] not in mutable:
            assert sha(ROOT/row['path']) == row['sha256'], row['path']

def raw_index(paths):
    return [dict(path=Path(p).resolve().as_posix(), sha256=sha(p)) for p in sorted(set(map(Path, paths)))]
