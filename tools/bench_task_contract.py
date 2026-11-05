#!/usr/bin/env python3
"""Scaffold and validate Bench task intake; never grant dataset admission."""
import argparse
import hashlib
import json
from pathlib import Path

ABILITIES = ('knowledge', 'reasoning', 'agentic-lean')
FILES = ('instruction.md', 'environment/manifest.json', 'solution/reference.txt', 'tests/contract.json')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def seal(root, task):
    value = {k: v for k, v in task.items() if k != 'contract_sha256'}
    value['files'] = {name: sha((root/name).read_bytes()) for name in FILES}
    return sha(json.dumps(value, sort_keys=True, separators=(',', ':')).encode())


def validate(root):
    root = root.resolve()
    task = json.loads((root/'task.json').read_text(encoding='utf-8'))
    if task['schema_version'] != 1 or task['stage'] not in ('draft', 'candidate'):
        raise ValueError('Intake accepts draft/candidate only; admission is a separate reviewed release')
    if task['ability'] not in ABILITIES or task['answer_format'] not in ('natural-language', 'lean'):
        raise ValueError('Unknown ability or answer format')
    if task['ability'] == 'agentic-lean' and task['answer_format'] != 'lean':
        raise ValueError('Agentic Lean requires Lean artifacts')
    if task['split'] != 'dev':
        raise ValueError('Intake is public dev; held-out splits require a separate leakage-reviewed release')
    for name in FILES:
        path = root/name
        if path.is_symlink() or not path.is_file() or not path.read_text(encoding='utf-8').strip():
            raise ValueError('Missing or linked package file: '+name)
    env = json.loads((root/'environment/manifest.json').read_text())
    tests = json.loads((root/'tests/contract.json').read_text())
    if env['agent_visible'] != ['instruction.md', 'environment/workspace']:
        raise ValueError('Agent inputs must exclude solution and verifier data')
    if any(type(task['budgets'].get(k)) is not int or task['budgets'][k] <= 0 for k in ('wall_seconds', 'tool_calls', 'tokens')):
        raise ValueError('Positive integer resource caps required')
    if task['access'] not in ('closed-book', 'text-retrieval', 'graph-retrieval', 'lean-assisted'):
        raise ValueError('Unknown access condition')
    if task['contract_sha256'] != seal(root, task):
        raise ValueError('Task or package changed after sealing')
    if task['stage'] == 'candidate':
        import re
        if not re.fullmatch('[0-9a-f]{40}', task['source_snapshot']):
            raise ValueError('Candidate needs immutable source commit')
        if not task['family'] or not task['graph_anchors'] or not task['license_scope'].strip():
            raise ValueError('Candidate requires family, licensing and graph anchors')
        if any(a['relation'] not in ('formal-target', 'source-correspondence', 'context-only') or not a['id'].startswith('declaration:') for a in task['graph_anchors']):
            raise ValueError('Invalid graph relation or declaration ID')
        if not env['toolchain'] or not env['dependency_lock_sha256'] or not env['isolation_receipt']:
            raise ValueError('Candidate requires pinned environment and isolation evidence')
        if tests['grader'] not in ('lean-kernel', 'expert-rubric'):
            raise ValueError('Candidate requires an implemented assessment method')
        expected = {'reference': 'pass', 'no-op': 'fail', 'wrong-answer': 'fail', 'placeholder': 'fail'}
        if tests['expected_controls'] != expected:
            raise ValueError('All positive and negative controls required')
        if task['ability'] == 'agentic-lean' and not tests['trajectory_required']:
            raise ValueError('Agentic Lean requires an inspectable tool trajectory')
        evidence = task['evidence']
        if set(evidence) != {'reference', 'negative-controls', 'semantic-review', 'leakage-review'}:
            raise ValueError('Candidate evidence incomplete')
        for record in evidence.values():
            path = (root/record['file']).resolve()
            if root not in path.parents or path.is_symlink() or sha(path.read_bytes()) != record['sha256']:
                raise ValueError('Evidence is missing, escapes the package or has changed')
        roles = task['review_roles']
        if set(roles) != {'author', 'blind_decoder', 'source_reviewer'} or any(not x.strip() for x in roles.values()) or len(set(roles.values())) != 3:
            raise ValueError('Distinct named semantic review actors required')
    return task


def scaffold(output, identity, ability):
    output.mkdir(parents=True, exist_ok=False)
    for folder in ('environment/workspace', 'solution', 'tests'):
        (output/folder).mkdir(parents=True)
    (output/'instruction.md').write_text('Draft authoring task: specify one precise Bandit/RL mathematical objective and its assumptions. Replace before candidate review.\n')
    (output/'solution/reference.txt').write_text('Draft: add a justified reference solution; this template is not a benchmark task.\n')
    env = dict(agent_visible=['instruction.md', 'environment/workspace'], toolchain='', dependency_lock_sha256='', isolation_receipt='')
    tests = dict(trajectory_required=ability == 'agentic-lean', expected_controls={'reference':'pass','no-op':'fail','wrong-answer':'fail','placeholder':'fail'}, grader='unimplemented')
    for name, value in [('environment/manifest.json', env), ('tests/contract.json', tests)]:
        (output/name).write_text(json.dumps(value, indent=2)+'\n')
    task = dict(schema_version=1, id=identity, stage='draft', ability=ability,
                answer_format='lean' if ability == 'agentic-lean' else 'natural-language', family='', split='dev',
                source_snapshot='', graph_anchors=[], license_scope='', access='lean-assisted' if ability == 'agentic-lean' else 'closed-book',
                budgets=dict(wall_seconds=600, tool_calls=100, tokens=20000), evidence={}, review_roles={})
    task['contract_sha256'] = seal(output, task)
    (output/'task.json').write_text(json.dumps(task, indent=2)+'\n')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='command', required=True)
    s = sub.add_parser('scaffold'); s.add_argument('--id', required=True); s.add_argument('--ability', choices=ABILITIES, required=True); s.add_argument('--output', type=Path, required=True)
    v = sub.add_parser('validate'); v.add_argument('package', type=Path)
    all_tasks = sub.add_parser('validate-all')
    all_tasks.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1]/'benchmarks/banditrlbench/tasks')
    args = p.parse_args()
    if args.command == 'validate-all':
        packages = sorted(args.root.glob('*/task.json'))
        for package in packages:
            validate(package.parent)
        print(json.dumps(dict(packages_checked=len(packages), admission='not-granted')))
        return
    if args.command == 'scaffold':
        scaffold(args.output, args.id, args.ability)
        root = args.output
    else:
        root = args.package
    task = validate(root)
    print(json.dumps(dict(id=task['id'], stage=task['stage'], contract='valid', admission='not-granted', semantic_correctness='not-established-by-intake')))


if __name__ == '__main__':
    main()
