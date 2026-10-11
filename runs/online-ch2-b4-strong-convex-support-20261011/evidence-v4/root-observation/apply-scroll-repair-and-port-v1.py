import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

root = Path('E:/ABRL/worktrees/research-online-book')
proposal = root / 'tmp/online-support-formula-scroll-affordance-repair-20261012'
destination = root / 'runs/online-ch2-b4-strong-convex-support-20261011/evidence-v4'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
git = lambda *a: subprocess.check_output(['git', '-c', 'core.longpaths=true', *a], cwd=root)
head = '95cfc51fa11619217f8153614d5b5b8a6c04aa2d'
assert git('rev-parse', 'HEAD').decode().strip() == head
assert git('branch', '--show-current').decode().strip() == 'codex/research-online-ch2-strong-convex-support'
assert not git('status', '--porcelain=v1', '-z')
plan_path = proposal / 'application-plan-v1.json'
assert digest(plan_path) == '86073ee284defe8142c4c9f4faa214e5fb6b1bb71febd1ce57921ddf71a9fb38'
plan = json.loads(plan_path.read_bytes())
review = root / 'tmp/online-support-formula-scroll-affordance-source-review-20261012/concrete-application-source-verdict-v1.json'
assert digest(review) == '899d6f15d0667abc9bc998d449c02aa1023bfd697f2094979e055d048cc27e98'
assert json.loads(review.read_bytes())['verdict'] == 'PASS_BOUNDED_EXACT_CSS_MAINTENANCE_APPLICATION_ELIGIBILITY'
for row in plan['files']:
    target = root / row['target']
    candidate = root / row['candidate']
    assert digest(candidate) == row['candidate_sha256']
    if row.get('base_must_be_absent'):
        assert not target.exists()
    else:
        assert digest(target) == row['base_sha256']
spec = importlib.util.spec_from_file_location('native_validator', root / 'tools/check_contributor_contract.py')
validator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(validator)
_, errors = validator.validate_contract(root / plan['files'][1]['candidate'])
assert not errors, errors
assert not destination.exists()
selected = []
excluded = []
def select_tree(folder, prefix, predicate=lambda p: True):
    assert folder.is_dir(), folder
    for source in sorted(folder.rglob('*')):
        if source.is_file():
            if predicate(source):
                selected.append((source, Path(prefix) / source.relative_to(folder)))
            else:
                excluded.append({'source': source.relative_to(root).as_posix(), 'bytes': source.stat().st_size,
                                 'sha256': digest(source), 'disposition': 'Original retained in ignored execution directory; no deletion or relabeling.'})
select_tree(root / 'tmp/online-support-owner-repaired-gates-20261012', 'original-95c-gates')
select_tree(proposal, 'scroll-repair-proposal')
select_tree(review.parent, 'scroll-repair-source-review')
tool_dir = root / 'tmp/online-support-reader-tool-preparation-20261012'
for source in sorted(tool_dir.iterdir()):
    if source.is_file():
        selected.append((source, Path('reader-tool-preparation') / source.name))
for version in range(2, 7):
    select_tree(tool_dir / f'actual-render-v{version}', f'actual-render-v{version}',
                lambda p: p.suffix == '.png' or p.name == 'failure-dom.html'
                or p.name == 'reconciliation-render-failure-v1.json'
                or ('clipping' in p.name and p.suffix == '.json'))
source_dir = root / 'tmp/online-support-reader-source-review-20261012'
for source in sorted(source_dir.glob('*.json')):
    selected.append((source, Path('partial-reader-source-review') / source.name))
resume_names = ['owner-repaired-gates-v1.py', 'owner-repaired-gate-plan-v1.json',
                'parse-owner-repaired-axioms-v1.py', 'owner-repaired-combined-axiom-parsed-v1.json',
                'prepare-owner-repaired-structural-v1.py', 'browser-execution-argv-v2.json',
                'browser-capability-observation-v1.json', 'pr228-delivery-observation-v1.json',
                'record-pr228-delivery-v1.py', 'pr228-ci-observation-v1.json', 'record-pr228-ci-v1.py',
                'pr228-ci-snapshot-v1-stdout.raw', 'pr228-ci-snapshot-v1-stderr.raw',
                'pr228-push-failure-v1-stdout.raw', 'pr228-push-failure-v1-stderr.raw',
                'support-pr-body-v1.md', 'apply-scroll-repair-and-port-v1.py']
for version in range(3, 7):
    resume_names.extend([f'run-reader-successor-v{version}.py', f'browser-execution-v{version}-start.json',
                         f'browser-execution-v{version}-result.json'])
for name in resume_names:
    source = Path(__file__).parent / name
    assert source.is_file(), source
    selected.append((source, Path('root-observation') / name))
assert len({str(relative) for _, relative in selected}) == len(selected)
for label in ['contributor-actual-pr-base-v1', 'process-memory-v1', 'production-root-v1', 'shared-Tests-v1',
              'full-harness-v1', 'combined-axiom-audit-v1', 'plain-site-build-v1', 'plain-site-check-v1',
              'verified-site-build-v1', 'verified-site-check-v1']:
    receipt = json.loads((root / 'tmp/online-support-owner-repaired-gates-20261012' / label / 'receipt.json').read_bytes())
    assert receipt['actual_exit'] == 0 and receipt['capture_integrity_ok']
    assert receipt['complete_source_path_set_and_RAW_unchanged']
    assert receipt['pre_git']['HEAD'] == receipt['post_git']['HEAD'] == head
    assert receipt['pre_git']['status_porcelain_v1_z_hex'] == receipt['post_git']['status_porcelain_v1_z_hex'] == ''
destination.mkdir()
rows = []
for source, relative in selected:
    target = destination / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open('xb') as stream:
        stream.write(source.read_bytes())
    assert digest(source) == digest(target)
    rows.append({'source': source.relative_to(root).as_posix(), 'copy': target.relative_to(root).as_posix(),
                 'sha256': digest(target), 'bytes': target.stat().st_size})
for row in plan['files']:
    target = root / row['target']
    if row.get('base_must_be_absent'):
        with target.open('xb') as stream:
            stream.write((root / row['candidate']).read_bytes())
    else:
        target.write_bytes((root / row['candidate']).read_bytes())
    assert digest(target) == row['candidate_sha256']
record = {'historical_source_head': head, 'historical_gate_actual_exits': [0] * 10,
          'historical_browser_actual_exits': {'actual-render-v2': 1, 'actual-render-v3': 1,
                                            'actual-render-v4': 1, 'actual-render-v5': 1, 'actual-render-v6': 1},
          'historical_full_reader_accepted': False, 'historical_failures_not_relabelled': True,
          'new_source_requires_fresh_gates_and_complete_pixels': True,
          'mathematical_targets_or_dependencies_removed': 0, 'Lean_changes': 0,
          'application_plan_sha256': digest(plan_path), 'source_review_sha256': digest(review),
          'applied_files': plan['files'], 'rows': rows, 'excluded_originals_retained': excluded,
          'copied_bytes': sum(row['bytes'] for row in rows), 'global_goal_complete': False}
with (destination / 'exact-port-and-application-v1.json').open('x', encoding='utf-8', newline='\n') as stream:
    json.dump(record, stream, ensure_ascii=False, indent=2)
    stream.write('\n')
print(json.dumps({'copied_files': len(rows), 'copied_bytes': record['copied_bytes'],
                  'excluded_originals_retained': len(excluded), 'fresh_gates_pending': True}))
