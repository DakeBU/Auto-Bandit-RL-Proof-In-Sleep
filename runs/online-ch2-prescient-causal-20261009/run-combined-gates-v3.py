from publication_guard_v4 import *
import re
fixed()
capture('pre-harness-track-new-Lean-v2', 'git', 'add', PUBLIC.relative_to(ROOT).as_posix(), CANARY.relative_to(ROOT).as_posix())
rows_out = []
for label, target in [('combined-root-v2', 'BanditRLProof'), ('combined-Tests-v2', 'Tests')]:
    code, out = capture(label, 'lake', 'build', target, required=False)
    jobs = list(map(int, re.findall(r'Build completed successfully \((\d+) jobs\)', out)))
    assert code == 0 and jobs and 'Lean exited with code 1' not in out and 'error: build failed' not in out, out[-10000:]
    rows_out.append(dict(target=target, actual_exit=code, actual_cached_inclusive_success_jobs=jobs,
        receipt_sha256=sha(RUN / (label + '.json'))))
    fixed()
write(RUN / 'combined-root-Tests-inspected-v2.json', dict(rows=rows_out,
    actual_root_Tests_passed=True, production_sha256=sha(PUBLIC), canary_sha256=sha(CANARY),
    root_sha256=sha(ROOT / 'BanditRLProof.lean'), Tests_root_sha256=sha(ROOT / 'Tests.lean'),
    full_harness_pending=True, chapter_complete=False, whole_Goal_status='ACTIVE'))
code, out = capture('combined-full-harness-v2', sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', 'check', required=False)
jobs = list(map(int, re.findall(r'Build completed successfully \((\d+) jobs\)', out)))
tests = re.findall(r'Ran (\d+) tests in ([\d.]+)s', out)
assert code == 0 and jobs and tests and re.search(r'\nOK(?: \(skipped=\d+\))?\s', out) and 'check passed' in out, out[-16000:]
assert 'error: build failed' not in out and 'Lean exited with code 1' not in out and 'forbidden placeholder scan failed' not in out and 'tools/ProofGraphExport.lean' in out
fixed()
write(RUN / 'full-harness-inspected-v2.json', dict(actual_exit=code,
    actual_successful_cached_inclusive_build_jobs=jobs,
    actual_unittest_runs=[dict(tests=int(n), seconds=float(s)) for n, s in tests],
    actual_skip_markers=re.findall(r'OK \(skipped=(\d+)\)', out), actual_check_passed=True,
    actual_ProofGraphExport_compile_present=True,
    actual_command_receipt_sha256=sha(RUN / 'combined-full-harness-v2.json'),
    applicable_production_sha256=sha(PUBLIC), applicable_canary_sha256=sha(CANARY),
    applicable_root_sha256=sha(ROOT / 'BanditRLProof.lean'), applicable_Tests_root_sha256=sha(ROOT / 'Tests.lean'),
    source_pins={p: sha(ROOT / p) for p in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']},
    site_registry_pixels_FINAL_native_delivery_pending=True, source_container_closed=False,
    chapter_complete=False, whole_Goal_status='ACTIVE'))
print('Actual combined root/Tests/full harness compiler/unittest/exporter/check markers inspected.')
