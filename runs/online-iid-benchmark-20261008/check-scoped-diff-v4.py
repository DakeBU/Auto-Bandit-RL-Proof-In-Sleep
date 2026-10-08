from common_integrated_v2 import *
fixed_integrated()
exceptions=load(RUN/'diff-raw-bound-exceptions-v4.json')['exceptions']
assert len(exceptions)==7
expected={'blind-reconstruction-v1.md','combined-root-v2.log','combined-Tests-v2.log','full-harness-v2.log',
    'common_v1.py','common_reviewed_v2.py','pre-source-full-diff-v3.log'}
assert {Path(r['path']).name for r in exceptions}==expected
for row in exceptions: assert sha(row['path'])==row['sha256'],row['path']
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--check',BASE,'--','.',
    *[':(exclude)'+r['path'] for r in exceptions]]
child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
sys.stdout.write(child.stdout.decode('utf8',errors='replace'))
assert child.returncode==0,child.returncode
write(RUN/('scoped-diff-'+sys.argv[1]+'.json'),dict(command=command,actual_exit_code=child.returncode,
    exact_raw_byte_exceptions=exceptions,all_public_Tests_readers_contracts_and_nonexempt_helpers_checked=True,
    two_frozen_protocol_helpers_exception_only_at_EOF=True,full_unexcluded_diff_exit=2,
    package_accepted=False,chapter_complete=False,goal_complete=False))
