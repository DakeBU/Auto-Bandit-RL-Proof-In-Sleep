from delivery_guard_20261011_v2 import *
a=arguments();fixed(a);gate=load(RUN/('full-harness-inspected-'+a.tag+'.json'))
assert gate['actual_exit']==0 and gate['actual_check_passed'] and gate['actual_ProofGraphExport_compile_present']
r=gate['command_receipt'];assert sha(r['path'])==r['sha256'];d,out=output_of(r['path'])
assert d['command'][-2:]==['tools/bandit.py','check'] and 'check passed' in out
same_binding(gate['source_binding'])
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,encoding='utf8').strip()
status=subprocess.check_output(['git','status','--porcelain=v1','-z'],cwd=ROOT)
assert not status or a.allow_dirty_local_site,'Default requires clean source at site start; parent must explicitly choose dirty local preview'
site=ROOT/'tmp'/('online-ch2-adaptive-osd-site-'+a.tag)
assert not site.exists(),'Create-only output directory required'
# No commit, staging, acceptance or deployment command is present here.
capture('site-build-'+a.tag,sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site)
m=load(site/'site-manifest.json')
assert m['lean_verified'] and m['source_commit']==head
assert m['source_dirty']==bool(status)
fixed(a);same_binding(gate['source_binding'])
capture('site-check-'+a.tag,sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
write(RUN/('site-binding-'+a.tag+'.json'),dict(site=site.as_posix(),head=head,source_dirty=bool(status),lean_verified=True,full_harness=rows([RUN/('full-harness-inspected-'+a.tag+'.json')]),source_binding=gate['source_binding'],manifest=rows([site/'site-manifest.json']),deployed=False,boundary='Local preview only; rendered-pixel and postcommit exact-head delivery review separate; dirty local build never claimed clean'))
