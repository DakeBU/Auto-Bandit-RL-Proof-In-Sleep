import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

root = Path('E:/ABRL/worktrees/research-online-book')
base = root / 'tmp/online-support-teaching-owner-repair-20261012'
dest = root / 'runs/online-ch2-b4-strong-convex-support-20261011/evidence-v3'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
git = lambda *a: subprocess.check_output(['git', '-c', 'core.longpaths=true', *a], cwd=root)
assert git('rev-parse', 'HEAD').decode().strip() == 'ceef2d303da1398bd543d144930e3ec7e1b58263'
assert not git('status', '--porcelain=v1', '-z')
target = root / 'website/content/readings.json'
candidate = base / 'readings-candidate-v1.json'
assert digest(target) == '5100d9b77ec4e76014ef448c7833e36987280389a0605b9a5c8b30de5db4e9ca'
assert digest(candidate) == 'b889b838f18aa4427c50d0ea130b0b1dc33bac9c8c4c8595f988f19261d7ad80'
review = root / 'tmp/online-support-teaching-owner-source-review-20261012/owner-repair-source-review-v1.json'
assert digest(review) == '01a47ede6ef71e21338f4e27513ceeb6f56dea4d05b22ff27fd01e103f2bfeeb'
native = base / 'ONLINE-SUBGRADIENT-INTERIOR-TEACHING-OWNER-20261012.json'
assert digest(native) == '0bba285ac59cf9d2bbf776867a865ec75fd2569f349bc2a4bf062ffc3caf64a0'
ms = importlib.util.spec_from_file_location('native_validator', root / 'tools/check_contributor_contract.py')
module = importlib.util.module_from_spec(ms)
ms.loader.exec_module(module)
_, errors = module.validate_contract(native)
assert errors == [], errors
before = json.loads(target.read_bytes())
after = json.loads(candidate.read_bytes())
row = next(r for r in before['readings'] if r['slug'] == 'online-subgradient-interior')
assert row['teaching_route'].pop(0) == 'BanditRL.OnlineConvex.affine_support_of_domain_interior'
assert before == after
assert not dest.exists()
dest.mkdir()
target.write_bytes(candidate.read_bytes())
native_target = root / 'research-wiki/contribution-contracts' / native.name
with native_target.open('xb') as stream:
    stream.write(native.read_bytes())
rows = []
def port(source, relative):
    output = dest / relative
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open('xb') as stream:
        stream.write(source.read_bytes())
    assert digest(source) == digest(output)
    rows.append({'source': source.relative_to(root).as_posix(), 'copy': output.relative_to(root).as_posix(), 'sha256': digest(output), 'bytes': output.stat().st_size})
for folder, prefix in [
 (root / 'tmp/online-ch2-b4-strong-convex-support-gates-20261011', 'original-ceef-gates'),
 (base, 'owner-repair-proposal'),
 (review.parent, 'owner-repair-source-review'),
]:
    for path in sorted(folder.rglob('*')):
        if path.is_file():
            port(path, str(Path(prefix) / path.relative_to(folder)))
for name in ['resume-gates-v1.py', 'interrupted-Tests-observation-v1.json', 'site-and-axiom-gates-v1.py', 'combined-axiom-parsed-v1.json', 'browser-capability-observation-v1.json', 'apply-owner-repair-and-port-v1.py']:
    port(Path(__file__).parent / name, 'root-observation/' + name)
record = {
 'kind': 'Exact evidence copies and bounded reader-navigation repair; no new verification execution',
 'original_gate_source_head': 'ceef2d303da1398bd543d144930e3ec7e1b58263',
 'successful_original_gates': ['production-root-v1', 'shared-Tests-v2-thread-limit', 'full-harness-v1-thread-limit', 'combined-axiom-audit-v1-thread-limit', 'contributor-actual-pr-base-v1', 'process-memory-v1'],
 'original_failures_preserved': ['shared-Tests-v1 interrupted environment failure without final exit', 'contributor-pinned-main-base-v1 actual1', 'plain-site-build-v1 actual1'],
 'no_relabel_to_new_head': True,
 'new_candidate_requires_new_gates_and_pixels': True,
 'application': {'readings_before_sha256': '5100d9b77ec4e76014ef448c7833e36987280389a0605b9a5c8b30de5db4e9ca', 'readings_after_sha256': digest(target), 'native_sha256': digest(native_target), 'source_review_sha256': digest(review), 'removed_navigation_references': 1, 'mathematical_targets_removed': 0, 'dependency_edges_removed': 0, 'Lean_proof_changes': 0},
 'rows': rows,
 'total_copied_bytes': sum(r['bytes'] for r in rows),
 'global_goal_complete': False,
}
with (dest / 'exact-port-and-application-v1.json').open('x', encoding='utf-8', newline='\n') as stream:
    json.dump(record, stream, ensure_ascii=False, indent=2)
    stream.write('\n')
print(json.dumps({'copied_files': len(rows), 'bytes': record['total_copied_bytes'], 'readings_sha256': digest(target), 'new_gates_pending': True}))
