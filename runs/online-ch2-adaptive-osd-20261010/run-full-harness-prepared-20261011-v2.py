from delivery_guard_20261011_v2 import *
a=arguments();fixed(a,require_index=True);roots=require_roots();binding=source_binding()
label='full-harness-'+a.tag
code,out=capture(label,sys.executable,'-B','-X','utf8','tools/bandit.py','check',required=False)
# Always retain command output before interpreting success/failure.
assert code==0,out[-12000:]
jobs=re.findall(r'Build completed successfully \((\d+) jobs\)',out)
tests=re.findall(r'Ran (\d+) tests in ([\d.]+)s',out)
assert jobs and tests and re.search(r'\nOK(?: \(skipped=\d+\))?\s',out)
assert 'check passed' in out and 'tools/ProofGraphExport.lean' in out
assert all(x not in out for x in ['error: build failed','Lean exited with code 1','forbidden placeholder scan failed'])
fixed(a,require_index=True);same_binding(binding)
write(RUN/('full-harness-inspected-'+a.tag+'.json'),dict(actual_exit=0,actual_check_passed=True,actual_ProofGraphExport_compile_present=True,root_receipts=roots,command_receipt=rows([RUN/(label+'.json')])[0],source_binding=binding,cached_inclusive_build_jobs=list(map(int,jobs)),unittest_runs=tests,skip_markers=re.findall(r'OK \(skipped=(\d+)\)',out),review=rows([a.review]),native_package_chapter_acceptance=False,site_and_delivery='pending'))
