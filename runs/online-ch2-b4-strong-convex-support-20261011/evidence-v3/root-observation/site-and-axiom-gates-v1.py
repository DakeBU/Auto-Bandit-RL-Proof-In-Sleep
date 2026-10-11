import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

root = Path('E:/ABRL/worktrees/research-online-book')
py = 'C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
plan = json.loads((root / 'runs/online-ch2-b4-strong-convex-support-20261011/prepared/sequential-lean-gate-plan-v1.json').read_text())
head = 'ceef2d303da1398bd543d144930e3ec7e1b58263'
run = root / plan['run']
for label in ['production-root-v1', 'shared-Tests-v2-thread-limit', 'full-harness-v1-thread-limit']:
    row = json.loads((run / label / 'receipt.json').read_text())
    assert row['actual_exit'] == 0 and row['capture_integrity_ok']
    assert row['pre_git']['HEAD'] == row['post_git']['HEAD'] == head
    assert row['complete_source_path_set_and_RAW_unchanged']
    assert row['pre_git']['status_porcelain_v1_z_hex'] == row['post_git']['status_porcelain_v1_z_hex'] == ''
site = 'tmp/online-support-site-20261012-verified-v1'
plain = 'tmp/online-support-site-20261012-plain-v1'
assert not (root / site).exists() and not (root / plain).exists()
wrapper = [py, '-B', '-X', 'utf8', '-c', "import os,subprocess,sys; env=dict(os.environ,LEAN_NUM_THREADS='2'); sys.exit(subprocess.call(sys.argv[1:],env=env))"]
gates = [
    ('combined-axiom-audit-v1-thread-limit', ['lake', 'env', 'lean', 'docs/contracts/online-ch2-b4-strong-convex-support-v1/combined-axiom-audit-probe-v1.lean']),
    ('plain-site-build-v1', [py, '-B', '-X', 'utf8', 'website/scripts/build_site.py', '--output', plain]),
    ('plain-site-check-v1', [py, '-B', '-X', 'utf8', 'website/scripts/check_site.py', '--output', plain, '--allow-unverified']),
    ('verified-site-build-v1', [py, '-B', '-X', 'utf8', 'website/scripts/build_site.py', '--output', site, '--lean-verified']),
    ('verified-site-check-v1', [py, '-B', '-X', 'utf8', 'website/scripts/check_site.py', '--output', site]),
]
for label, command in gates:
    argv = [py, '-B', '-X', 'utf8', plan['helper'], '--root', str(root), '--run', plan['run'], '--label', label]
    for contract in plan['leaf_contracts']:
        argv += ['--leaf-contract', contract]
    argv += ['--'] + wrapper + command
    print(json.dumps({'starting': label, 'argv': argv}), flush=True)
    result = subprocess.run(argv, cwd=root)
    if result.returncode:
        sys.exit(result.returncode)
    if label.startswith('combined-axiom'):
        output = (run / label / 'stdout.raw').read_bytes()
        matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output.decode('utf-8'))
        assert len(matches) == 10, matches
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        parsed = {name: [x.strip() for x in axioms.split(',') if x.strip()] for name, axioms in matches}
        assert all(set(axioms) <= allowed for axioms in parsed.values()), parsed
        with (Path(__file__).parent / 'combined-axiom-parsed-v1.json').open('x', encoding='utf-8') as stream:
            json.dump({'kind': 'parsed actual audit stdout', 'source_head': head, 'stdout_sha256': hashlib.sha256(output).hexdigest(), 'declarations': parsed, 'no_extra_axioms': True}, stream, indent=2)
