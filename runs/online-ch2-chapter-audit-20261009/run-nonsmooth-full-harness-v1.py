from common_nonsmooth_publication_v2 import *
import re

fixed()
assert load(RUN/'nonsmooth-combined-root-Tests-inspected-v1.json')['actual_root_Tests_passed']
code,out=capture('nonsmooth-combined-full-harness-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','check',required=False)
assert code==0
jobs=list(map(int,re.findall(r'Build completed successfully \((\d+) jobs\)',out)))
assert jobs and 'error: build failed' not in out and 'Lean exited with code 1' not in out
tests=re.findall(r'Ran (\d+) tests in ([\d.]+)s',out)
assert tests and re.search(r'\nOK(?: \(skipped=\d+\))?\s',out) and 'check passed' in out
assert 'forbidden placeholder scan failed' not in out and 'tools/ProofGraphExport.lean' in out
fixed()
write(RUN/'nonsmooth-full-harness-inspected-v1.json',dict(
    actual_exit=0,actual_successful_cached_inclusive_build_jobs=jobs,
    actual_unittest_runs=[dict(tests=int(n),seconds=float(s)) for n,s in tests],
    actual_skip_markers=re.findall(r'OK \(skipped=(\d+)\)',out),
    actual_check_passed=True,actual_ProofGraphExport_compile_present=True,
    actual_command_receipt_sha256=sha(RUN/'nonsmooth-combined-full-harness-v1.json'),
    applicable_production_sha256=sha(PUBLIC),applicable_canary_sha256=sha(CANARY),
    applicable_root_sha256=sha(ROOT/'BanditRLProof.lean'),applicable_Tests_root_sha256=sha(ROOT/'Tests.lean'),
    fixed_source_pins={p:sha(ROOT/p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']},
    source_semantic_reader_and_site_FINAL_separate=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
print('Actual full harness compiler/unittest/exporter/check markers inspected; site/FINAL/delivery remain separate.')
