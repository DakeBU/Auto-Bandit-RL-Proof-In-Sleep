from integration_guard_v2 import *
import re
fixed()
assert load(RUN/'candidate-stage-inspected-v1.json')['actual_active_text_diff_exit']==0
for p in [MODULE,TEST]:assert subprocess.check_output(['git','show',':'+p.relative_to(ROOT).as_posix()])==p.read_bytes()
code,out=capture('combined-full-harness-v2',sys.executable,'-B','-X','utf8','tools/bandit.py','check',required=False)
jobs=list(map(int,re.findall(r'Build completed successfully \((\d+) jobs\)',out)))
tests=re.findall(r'Ran (\d+) tests in ([\d.]+)s',out)
assert code==0 and jobs and tests and re.search(r'\nOK(?: \(skipped=\d+\))?\s',out) and 'check passed' in out,out[-16000:]
assert all(s not in out for s in ['error: build failed','Lean exited with code 1','forbidden placeholder scan failed'])
assert 'tools/ProofGraphExport.lean' in out
fixed()
write(RUN/'full-harness-inspected-v2.json',dict(actual_exit=code,cached_inclusive_successful_build_jobs=jobs,unittest_runs=[dict(tests=int(n),seconds=float(s)) for n,s in tests],skip_markers=re.findall(r'OK \(skipped=(\d+)\)',out),actual_check_passed=True,actual_ProofGraphExport_compile_present=True,command_receipt_sha256=sha(RUN/'combined-full-harness-v2.json'),production_sha256=sha(MODULE),Test_sha256=sha(TEST),root_sha256=sha(ROOT/'BanditRLProof.lean'),Test_root_sha256=sha(ROOT/'Tests.lean'),source_pins={p:sha(ROOT/p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']},actual_git_index_required_by_anonymous_supplement=True,prior_failed_receipt=sha(RUN/'full-harness-failure-inspected-v1.json'),site_registry_pixels_FINAL_native_delivery_pending=True,source_container_closed=False,chapter_complete=False,whole_Goal='active'))
print('Actual full harness v2 compiler/exporter/unittest markers inspected.',flush=True)
