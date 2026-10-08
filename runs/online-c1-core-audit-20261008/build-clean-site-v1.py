from common_integrated_v1 import *
fixed_integrated()
g=load(RUN/'combined-gates-v1.json')
assert g['actual_exit_codes']==[0,0,0] and sha(CANARY)==g['canary_sha256']
assert g['public_files_sha256']=={p.as_posix():sha(p) for p in MODULES}
assert all(sha(p)==h for p,h in g['source_pins'].items())
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
site=Path('tmp/online-c1-core-audit-site-v1');temporary=Path('tmp/online-c1-core-audit-site-build-v1.log')
assert not site.exists() and not temporary.exists()
command=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site.as_posix()]
tick=time.monotonic()
with temporary.open('wb') as stream: child=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v1.log',temporary.read_bytes())
write(RUN/'site-build-v1-exit.json',dict(command=command,cwd=ROOT.as_posix(),exit_code=child.returncode,
    seconds=time.monotonic()-tick,source_commit=head,actual_clean_tree_at_start=True,
    log_sha256=sha(RUN/'site-build-v1.log'),applicable_combined_gate_sha256=sha(RUN/'combined-gates-v1.json'),
    production_Lean_and_pins_unchanged=True,deployed=False))
assert child.returncode==0
gate('site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-check-v1',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
fixed_integrated()
print('Actual clean applicable local site and unchanged shared registry passed; current DOM/pixels/FINAL/native/delivery pending.')
