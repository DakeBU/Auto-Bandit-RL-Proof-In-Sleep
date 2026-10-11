from common import *
import re

production = [ROOT/'BanditRLProof'/name for name in
    ['OnlineAdaptivePotential.lean', 'OnlineAdaptiveOSD.lean', 'OnlineAdaptiveBenchmark.lean']]
tests = [ROOT/'Tests'/name for name in
    ['OnlineAdaptivePotentialCanary.lean', 'OnlineAdaptiveOSDCanary.lean']]
roots = [ROOT/'BanditRLProof.lean', ROOT/'Tests.lean']
pins = [ROOT/name for name in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']]
fixed = rows(production+tests+roots+pins)
for name in ['OnlineAdaptivePotential', 'OnlineAdaptiveOSD', 'OnlineAdaptiveBenchmark']:
    assert 'import BanditRLProof.'+name in roots[0].read_text(encoding='utf8').splitlines()
for name in ['OnlineAdaptivePotentialCanary', 'OnlineAdaptiveOSDCanary']:
    assert 'import Tests.'+name in roots[1].read_text(encoding='utf8').splitlines()

results = []
for label, target in [('combined-root-20261011-v1', 'BanditRLProof'),
                      ('combined-Tests-20261011-v1', 'Tests')]:
    code, out = capture(label, 'lake', 'build', target, required=False)
    jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', out)
    assert code == 0 and jobs, out[-12000:]
    assert 'error: build failed' not in out and 'Lean exited with code 1' not in out
    assert rows(production+tests+roots+pins) == fixed
    results.append(dict(target=target, actual_exit=code,
        cached_inclusive_jobs=list(map(int, jobs)),
        command_receipt_sha256=sha(RUN/(label+'.json'))))
write(RUN/'combined-root-Tests-inspected-20261011-v1.json', dict(
    fixed_inputs=fixed, results=results, root_Tests_passed=True,
    full_harness='required pending', source_semantic_status='separate reviews',
    site_registry_delivery='required pending', chapter_complete=False, goal='active'))
print('Combined shared-library root and public Tests passed; full harness/site/acceptance still required.', flush=True)
