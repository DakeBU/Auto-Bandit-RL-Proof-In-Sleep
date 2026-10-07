from common_integrated_v2 import *
fixed_integrated()
exceptions=load(RUN/'diff-raw-evidence-exceptions-v6.json')['exceptions']
for row in exceptions:assert sha(row['path'])==row['sha256'],row['path']
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--check',BASE,'--','.',*[':(exclude)'+r['path'] for r in exceptions]]
child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
sys.stdout.write(child.stdout.decode('utf8',errors='replace'));assert child.returncode==0,child.returncode
write(RUN/('diff-check-'+sys.argv[1]+'.json'),dict(status='passed',actual_command=command,exit_code=child.returncode,exact_raw_evidence_exceptions=exceptions,production_reader_contract_scripts_checked=True,source_types_unchanged=True,chapter_complete=False,goal_complete=False))
