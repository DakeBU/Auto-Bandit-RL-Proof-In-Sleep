from publication_guard_v1 import *
import re
fixed()
capture('pre-harness-track-new-Lean-v1', 'git', 'add', PUBLIC.relative_to(ROOT).as_posix(), TEST.relative_to(ROOT).as_posix())
checks = []
for label, target in [('combined-root-v1', 'BanditRLProof'), ('combined-Tests-v1', 'Tests')]:
    code, out = capture(label, 'lake', 'build', target, required=False)
    jobs = list(map(int, re.findall(r'Build completed successfully \((\d+) jobs\)', out)))
    assert code == 0 and jobs and 'Lean exited with code 1' not in out and 'error: build failed' not in out, out[-12000:]
    checks.append(dict(target=target, actual_exit=code, cached_inclusive_jobs=jobs, receipt_sha256=sha(RUN/(label+'.json'))))
    fixed()
write(RUN/'combined-root-Tests-inspected-v1.json', dict(rows=checks, root_Tests_passed=True,
    production_sha256=sha(PUBLIC), Test_sha256=sha(TEST), root_sha256=sha(ROOT/'BanditRLProof.lean'),
    Test_root_sha256=sha(ROOT/'Tests.lean'), full_harness_pending=True, chapter_complete=False, whole_Goal='ACTIVE'))
code, out = capture('combined-full-harness-v1', sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', 'check', required=False)
jobs = list(map(int, re.findall(r'Build completed successfully \((\d+) jobs\)', out)))
tests = re.findall(r'Ran (\d+) tests in ([\d.]+)s', out)
assert code == 0 and jobs and tests and re.search(r'\nOK(?: \(skipped=\d+\))?\s', out) and 'check passed' in out, out[-16000:]
assert all(s not in out for s in ['error: build failed','Lean exited with code 1','forbidden placeholder scan failed'])
assert 'tools/ProofGraphExport.lean' in out
fixed()
write(RUN/'full-harness-inspected-v1.json', dict(actual_exit=code,
    cached_inclusive_successful_build_jobs=jobs, unittest_runs=[dict(tests=int(n),seconds=float(s)) for n,s in tests],
    skip_markers=re.findall(r'OK \(skipped=(\d+)\)',out), actual_check_passed=True, actual_ProofGraphExport_compile_present=True,
    command_receipt_sha256=sha(RUN/'combined-full-harness-v1.json'), production_sha256=sha(PUBLIC), Test_sha256=sha(TEST),
    root_sha256=sha(ROOT/'BanditRLProof.lean'), Test_root_sha256=sha(ROOT/'Tests.lean'),
    source_pins={p:sha(ROOT/p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']},
    site_registry_pixels_FINAL_native_delivery_pending=True, source_container_closed=False, chapter_complete=False, whole_Goal='ACTIVE'))
print('Actual combined root/Tests/harness compiler, unittest and exporter markers inspected.',flush=True)
