from pathlib import Path
import hashlib, json, subprocess, sys, time

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[1]
TASK = 'ONLINE-KERNEL-CAUSAL-20261008'
BRANCH = 'codex/research-online-kernel-causal'
BASE = '4db37e090143760d99b9aedd026a72fa0f1f09ac'
CONTRACT = ROOT / 'docs/contracts/online-kernel-causal-v1'
PUBLIC = ROOT / 'BanditRLProof/OnlineGuessingKernelCausal.lean'
CANARY = ROOT / 'Tests/OnlineGuessingKernelCausalCanary.lean'
PDF = ROOT / '../research-online-ogd/tmp/pdfs/orabona-v10.pdf'
PDF_SHA = 'cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
load = lambda p: json.loads(Path(p).read_text(encoding='utf8'))

def write(p, value):
    p = Path(p)
    assert not p.exists(), p
    p.parent.mkdir(parents=True, exist_ok=True)
    data = value if isinstance(value, bytes) else (
        value.rstrip('\n') + '\n' if isinstance(value, str) else json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf8')
    p.write_bytes(data)

def gate(label, *args, required=True):
    out = RUN / (label + '.log')
    receipt = RUN / (label + '-exit.json')
    assert not out.exists() and not receipt.exists()
    start = time.monotonic()
    with out.open('wb') as stream:
        result = subprocess.run(list(map(str, args)), stdout=stream, stderr=subprocess.STDOUT)
    write(receipt, dict(command=list(map(str, args)), cwd=ROOT.as_posix(), actual_exit=result.returncode,
          seconds=time.monotonic() - start, log_sha256=sha(out)))
    print(label, 'actual exit', result.returncode, flush=True)
    if required:
        assert result.returncode == 0, label
    return result.returncode

def native(label, *args):
    return gate(label, sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', *args)

def raw_index(paths):
    return [dict(path=Path(p).resolve().as_posix(), sha256=sha(p)) for p in sorted(set(map(Path, paths)))]

def baseline_fixed(mutable=()):
    assert Path.cwd() == ROOT
    assert subprocess.check_output(['git', 'branch', '--show-current'], encoding='utf8').strip() == BRANCH
    assert sha(PDF) == PDF_SHA
    for row in load(RUN / 'draft-baseline-v1.json')['rows']:
        assert sha(ROOT / row['snapshot']) == row['sha256']
        if row['path'] not in mutable:
            assert sha(ROOT / row['path']) == row['sha256'], row['path']
