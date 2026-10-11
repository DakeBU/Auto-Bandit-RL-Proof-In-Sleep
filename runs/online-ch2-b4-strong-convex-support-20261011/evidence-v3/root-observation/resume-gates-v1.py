import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys

root = Path('E:/ABRL/worktrees/research-online-book')
py = 'C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
plan = json.loads((root / 'runs/online-ch2-b4-strong-convex-support-20261011/prepared/sequential-lean-gate-plan-v1.json').read_text())
old = root / plan['run'] / 'shared-Tests-v1'
audit = {
    'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'kind': 'retrospective interruption observation, not a contemporaneous gate receipt',
    'old_session': 77816,
    'old_session_status': 'unknown/missing on continuation',
    'actual_controller_exit': None,
    'actual_lake_exit': None,
    'partial_log_reports_lean_exit': 3221226505,
    'classification': 'ENV_RESOURCE_THREAD_CREATION',
    'no_success_claim': True,
    'files': {},
}
for path in sorted(old.iterdir()):
    if path.is_file():
        data = path.read_bytes()
        audit['files'][path.name] = {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
assert not (old / 'receipt.json').exists()
assert b'failed to create thread' in (old / 'stdout.raw').read_bytes()
audit['current_git_head'] = subprocess.check_output(['git', '-c', 'core.longpaths=true', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
audit['current_git_status_hex'] = subprocess.check_output(['git', '-c', 'core.longpaths=true', 'status', '--porcelain=v1', '-z'], cwd=root).hex()
assert audit['current_git_head'] == 'ceef2d303da1398bd543d144930e3ec7e1b58263'
assert not audit['current_git_status_hex']
prior = json.loads((old / 'pre-source-inputs.json').read_text())
audit['retrospective_raw_files_checked'] = len(prior)
audit['retrospective_raw_mismatches'] = [r['path'] for r in prior if hashlib.sha256((root / r['path']).read_bytes()).hexdigest() != r['raw_sha256']]
assert not audit['retrospective_raw_mismatches']
with (Path(__file__).parent / 'interrupted-Tests-observation-v1.json').open('x', encoding='utf-8') as stream:
    json.dump(audit, stream, indent=2)

# The process-local environment setting is explicit in the recorded argv.
# No project configuration or parent/global environment is modified.
env_wrapper = [py, '-B', '-X', 'utf8', '-c', "import os,subprocess,sys; env=dict(os.environ,LEAN_NUM_THREADS='2'); sys.exit(subprocess.call(sys.argv[1:],env=env))"]
for label, command in [
    ('shared-Tests-v2-thread-limit', ['lake', 'build', 'Tests']),
    ('full-harness-v1-thread-limit', [py, '-B', '-X', 'utf8', 'tools/bandit.py', 'check']),
]:
    argv = [py, '-B', '-X', 'utf8', plan['helper'], '--root', str(root), '--run', plan['run'], '--label', label]
    for contract in plan['leaf_contracts']:
        argv += ['--leaf-contract', contract]
    argv += ['--'] + env_wrapper + command
    print(json.dumps({'starting': label, 'argv': argv}), flush=True)
    result = subprocess.run(argv, cwd=root)
    if result.returncode:
        sys.exit(result.returncode)
