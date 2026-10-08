from pathlib import Path
import hashlib, json, subprocess, sys, time

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[1]
assert Path.cwd() == ROOT
BASE = 'bf9f896cdfebb2b836dacb01f3d4b209466c2100'
BASE_BRANCH = 'codex/research-online-benchmarks'
BASE_PR = 193
BRANCH = 'codex/research-online-iid'
TASK = 'ONLINE-IID-BENCHMARK-20261008'
CONTRACT = Path('docs/contracts/online-iid-benchmark-v1')
PUBLIC = Path('BanditRLProof/OnlineGuessingIIDBenchmark.lean')
CANARY = Path('Tests/OnlineGuessingIIDBenchmarkCanary.lean')
PDF = Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
PDF_SHA = 'cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
PRE = 'BanditRL.OnlineLearning.'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
load = lambda p: json.loads(Path(p).read_text(encoding='utf8'))

def write(p, value):
    p = Path(p)
    assert not p.exists(), p
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(value if isinstance(value, bytes) else
        (value.rstrip('\n') + '\n' if isinstance(value, str) else json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf8'))

def gate(label, *args):
    log, receipt = RUN / (label + '.log'), RUN / (label + '-exit.json')
    assert not log.exists() and not receipt.exists()
    start = time.time()
    with log.open('wb') as f:
        r = subprocess.run(list(map(str, args)), stdout=f, stderr=subprocess.STDOUT)
    write(receipt, dict(command=list(map(str, args)), cwd=ROOT.as_posix(), exit_code=r.returncode,
        seconds=round(time.time() - start, 3), log_sha256=sha(log)))
    print(label, 'exit', r.returncode, flush=True)
    if r.returncode:
        raise RuntimeError(label + ' failed; actual raw failure retained')

def native(label, *args):
    gate(label, sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', *args)

def fixed():
    assert sha(PDF) == PDF_SHA
    for p, h in load(RUN / 'draft-baseline-v1.json')['fixed_files'].items():
        assert sha(p) == h, p

