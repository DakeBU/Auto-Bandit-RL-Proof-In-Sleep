from common_body_v1 import *
fixed_integrated()
g=load(RUN/'combined-gates-v1.json')
assert g['actual_exit_codes']==[0,0,0] and sha(PUBLIC)==g['public_sha256'] and sha(CANARY)==g['canary_sha256']
assert all(sha(ROOT/p)==h for p,h in g['source_pins'].items())
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
site=ROOT/'tmp/online-ae-causal-site-v1';temporary=ROOT/'tmp/online-ae-causal-site-build-v1.log'
assert not site.exists() and not temporary.exists()
command=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site.as_posix()]
tick=time.monotonic()
with temporary.open('wb') as stream:child=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v1.log',temporary.read_bytes())
write(RUN/'site-build-v1-exit.json',dict(command=command,cwd=ROOT.as_posix(),actual_exit=child.returncode,
    seconds=time.monotonic()-tick,source_commit=head,actual_clean_tree_at_start=True,
    log_sha256=sha(RUN/'site-build-v1.log'),applicable_combined_gate_sha256=sha(RUN/'combined-gates-v1.json'),
    public_canary_and_pins_unchanged=True,deployed=False))
assert child.returncode==0
gate('site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-check-v1',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
fixed_integrated()
print('Actual applicable clean local site and registry pass; current pixels and FINAL/native pending.',flush=True)
