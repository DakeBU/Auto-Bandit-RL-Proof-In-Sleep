from common_v1 import *
fixed(integrated=True)
for label,p in [('contributor','tools/check_contributor_contract.py'),('site-build','website/scripts/build_site.py'),('site-check','website/scripts/check_site.py')]:gate('help-'+label+'-v1',sys.executable,'-B','-X','utf8',p,'--help')
baseline=Path('tmp/online-ftl-state-site-v4/books/registry.json')
assert sha(baseline)==load('runs/online-ftl-state-20261007/registry-v5.json')['registry_sha256']
assert len(load(baseline)['nodes'])==10835
write(RUN/'registry-base-snapshot-v1.json',baseline.read_bytes())
gate('combined-root-v1','lake','build')
gate('combined-Tests-v1','lake','build','Tests')
gate('full-harness-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
gate('contributor-exact-base-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
label='contributor-origin-main-diagnostic-v1';log=RUN/(label+'.log');assert not log.exists();start=time.time()
with log.open('wb') as stream:child=subprocess.run([sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main'],stdout=stream,stderr=subprocess.STDOUT)
write(RUN/(label+'-exit.json'),dict(command='tools/check_contributor_contract.py --base origin/main',cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log),purpose='Honest all-stacked main-relative diagnostic; failing unrelated legacy obligations are NOT waived'))
write(RUN/'integrated-gates-v1.json',dict(status='Actual root/Tests/fullharness/exact PR189 base contributor commands passed',root_log_sha256=sha(RUN/'combined-root-v1.log'),Tests_log_sha256=sha(RUN/'combined-Tests-v1.log'),harness_log_sha256=sha(RUN/'full-harness-v1.log'),contributor_log_sha256=sha(RUN/'contributor-exact-base-v1.log'),main_diagnostic_exit_code=child.returncode,existing_math_exact=True,new_production_math=0,canary_sha256=sha(CANARY),public_documentation_sha256=sha(PUBLIC),site_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False))
fixed(integrated=True);print('Integrated commands succeeded; actual main diagnostic exit',child.returncode,'; no chapter acceptance.')
