import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys

root = Path('E:/ABRL/worktrees/research-online-book')
py = 'C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
head = '95cfc51fa11619217f8153614d5b5b8a6c04aa2d'
def git(*args):
    return subprocess.check_output(['git', '-c', 'core.longpaths=true', *args], cwd=root)
assert git('rev-parse', 'HEAD').decode().strip() == head
assert not git('status', '--porcelain=v1', '-z')
old = json.loads((root / 'runs/online-ch2-b4-strong-convex-support-20261011/prepared/sequential-lean-gate-plan-v1.json').read_text())
helper = old['helper']
assert hashlib.sha256((root / helper).read_bytes()).hexdigest() == '40faf086d3662f68b3e91da0cea913216afe2e5e60d89217c0ae6d830a2eb273'
run = 'tmp/online-support-owner-repaired-gates-20261012'
assert not (root / run).exists()
plain = 'tmp/online-support-site-20261012-plain-v2'
verified = 'tmp/online-support-site-20261012-verified-v2'
assert not (root / plain).exists() and not (root / verified).exists()
env_wrapper = [py, '-B', '-X', 'utf8', '-c', "import os,subprocess,sys; env=dict(os.environ,LEAN_NUM_THREADS='2'); sys.exit(subprocess.call(sys.argv[1:],env=env))"]
p = [py, '-B', '-X', 'utf8']
gates = [
    ('contributor-actual-pr-base-v1', p + ['tools/check_contributor_contract.py', '--base', '20d223bb3f45a51e746310e74759ed2e89dd7944']),
    ('process-memory-v1', p + ['tools/check_process_memory.py']),
    ('production-root-v1', ['lake', 'build', 'BanditRLProof']),
    ('shared-Tests-v1', ['lake', 'build', 'Tests']),
    ('full-harness-v1', p + ['tools/bandit.py', 'check']),
    ('combined-axiom-audit-v1', ['lake', 'env', 'lean', 'docs/contracts/online-ch2-b4-strong-convex-support-v1/combined-axiom-audit-probe-v1.lean']),
    ('plain-site-build-v1', p + ['website/scripts/build_site.py', '--output', plain]),
    ('plain-site-check-v1', p + ['website/scripts/check_site.py', '--output', plain, '--allow-unverified']),
    ('verified-site-build-v1', p + ['website/scripts/build_site.py', '--output', verified, '--lean-verified']),
    ('verified-site-check-v1', p + ['website/scripts/check_site.py', '--output', verified]),
]
plan = dict(source_head=head, created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), helper=helper,
            run=run, contracts=old['leaf_contracts'], environment_wrapper=env_wrapper, gates=gates,
            known_unresolved='Optional origin/main provenance comparison and push CI are not repaired by this teaching-owner change.')
with (Path(__file__).parent / 'owner-repaired-gate-plan-v1.json').open('x', encoding='utf-8') as stream:
    json.dump(plan, stream, indent=2)
for label, command in gates:
    assert git('rev-parse', 'HEAD').decode().strip() == head
    assert not git('status', '--porcelain=v1', '-z')
    argv = p + [helper, '--root', str(root), '--run', run, '--label', label]
    for contract in old['leaf_contracts']:
        argv += ['--leaf-contract', contract]
    argv += ['--'] + env_wrapper + command
    print(json.dumps({'starting': label, 'argv': argv}), flush=True)
    result = subprocess.run(argv, cwd=root)
    print(json.dumps({'finished': label, 'controller_exit': result.returncode}), flush=True)
    if result.returncode:
        sys.exit(result.returncode)
