from common_integrated_v1 import *

fixed_integrated()
exceptions = load(RUN / 'diff-raw-evidence-exceptions-v2.json')['exceptions']
assert len(exceptions) == 5
for row in exceptions: assert sha(row['path']) == row['sha256'], row['path']
command = ['git', '-c', 'core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol', 'diff', '--check', BASE,
    '--', '.', *[':(exclude)' + row['path'] for row in exceptions]]
child = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
sys.stdout.write(child.stdout.decode('utf8', errors='replace'))
assert child.returncode == 0, child.returncode
write(RUN / ('scoped-diff-' + sys.argv[1] + '.json'), dict(command=command, actual_exit_code=child.returncode,
    exact_raw_evidence_exceptions=exceptions, all_production_readers_contracts_helpers_checked=True))
