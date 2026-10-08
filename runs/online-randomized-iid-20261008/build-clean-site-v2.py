from common_integrated_v2 import *

fixed_integrated()
assert load(RUN/'integrated-gates-v2.json')['affected_production_paths']==5
assert load(RUN/'combined-gates-v3.json')['public_sha256']==sha(PUBLIC)
assert load(RUN/'combined-gates-v3.json')['canary_sha256']==sha(CANARY)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
site=Path('tmp/online-randomized-iid-site-v2')
assert not site.exists()
temporary=Path('tmp/online-randomized-iid-site-build-v2.log')
assert not temporary.exists()
command=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site.as_posix()]
start=time.monotonic()
with temporary.open('wb') as stream:
    child=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v2.log',temporary.read_bytes())
write(RUN/'site-build-v2-exit.json',dict(command=command,cwd=ROOT.as_posix(),exit_code=child.returncode,
    seconds=time.monotonic()-start,log_sha256=sha(RUN/'site-build-v2.log'),actual_clean_tree_at_start=True,
    stdout_ignored_until_completion=True,
    applicable_Lean='Actual combined-root-v2/combined-Tests-v2/full-harness-v3; public/canary/imports/pins and all existing Lean remain byte-identical.',
    applicable_contributor='Actual committed exact b08 stacked-base gate: five production paths/one own schema2 contract.',
    deployed=False))
assert child.returncode==0
gate('site-check-v2',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-check-v2',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v2.py')
gate('current-reader-capture-v2',sys.executable,'-B','-X','utf8',RUN/'capture-reader-v2.py')
fixed_integrated()
print('Actual clean local site/static registry/current reader capture gates passed; pixel/FINAL/native acceptance pending.')
