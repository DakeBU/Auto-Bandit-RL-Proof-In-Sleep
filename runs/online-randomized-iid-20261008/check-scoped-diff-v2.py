from common_integrated_v2 import *

fixed_integrated()
exceptions=load(RUN/'diff-raw-bound-exceptions-v2.json')['exceptions']
assert len(exceptions)==5
expected={'combined-root-v2.log','combined-Tests-v2.log','full-harness-v2.log','full-harness-v3.log','source-full-diff-v2.log'}
assert {Path(r['path']).name for r in exceptions}==expected
for row in exceptions: assert sha(row['path'])==row['sha256'],row['path']
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol',
    'diff','--cached','--check',BASE,'--','.',*[':(exclude)'+row['path'] for row in exceptions]]
child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
sys.stdout.write(child.stdout.decode('utf8',errors='replace'))
assert child.returncode==0,child.returncode
write(RUN/('scoped-diff-'+sys.argv[1]+'.json'),dict(command=command,actual_exit_code=child.returncode,
    exact_raw_byte_exceptions=exceptions,all_production_Tests_reader_contract_and_executable_helpers_checked=True,
    executable_helper_exceptions=0,full_unexcluded_diff_exit=2,full_unexcluded_diff_passed=False,
    package_accepted=False,chapter_complete=False,goal_complete=False))
