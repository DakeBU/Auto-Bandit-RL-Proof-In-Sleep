#!/usr/bin/env python3
"""Reproducible public-dev QA preparation, expert review and trusted Lean replay.

This runner never calls a model/API. Lean replay executes code: use it only for
trusted inputs in a disposable environment. It is NOT a security sandbox.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from website.scripts import banditrlbench as registry

MODES = ('closed-book', 'text-retrieval', 'graph-retrieval', 'lean-assisted')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(value):
    return hashlib.sha256(value).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


def write_rows(path, rows):
    path.write_text(''.join(json.dumps(row, ensure_ascii=False) + '\n' for row in rows), encoding='utf-8')


def targets():
    return json.loads((ROOT / 'benchmarks/banditrlbench/targets.json').read_text(encoding='utf-8'))


def task_rows(data, track):
    rows = registry.prompts(data, track)
    for row in rows:
        if track == 'lean':
            target = targets()[row['core_id']]
            row.update(imports=target['imports'], target_signature=target['signature'],
                       target_sha256=digest(target['signature'].encode()))
    return rows


def fresh_output(path):
    path.mkdir(parents=True, exist_ok=False)


def receipt(command, data, mode, model, agent):
    return dict(schema_version=1, command=command, dataset_version=data['version'],
                registry_sha256=digest(registry.DATA.read_bytes()),
                runner_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                runner_dirty=bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT)),
                runner_files_sha256={name: digest((ROOT / name).read_bytes().replace(b'\r\n', b'\n')) for name in
                    ('tools/banditrlbench.py', 'website/scripts/banditrlbench.py', 'benchmarks/banditrlbench/targets.json')},
                created_at=datetime.now(timezone.utc).isoformat(), mode=mode, model=model, agent=agent,
                split='dev', held_out=False, model_called_by_runner=False,
                access_policy='Declared by operator; not mechanically enforced by this local runner.')


def read_predictions(path, data, track):
    expected = {row['core_id']: row for row in task_rows(data, track)}
    found = {}
    for line in path.read_text(encoding='utf-8').splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        cid = row.get('core_id')
        if cid not in expected or cid in found:
            raise ValueError('Unknown or duplicate prediction core')
        fields = ('contract_hash', 'track', 'target_sha256') if track == 'lean' else ('contract_hash', 'track')
        if any(row.get(key) != expected[cid][key] for key in fields):
            raise ValueError('Stale prediction contract or wrong track')
        field = 'proof' if track == 'lean' else 'response'
        if not isinstance(row.get(field), str):
            raise ValueError('Prediction must have a string ' + field)
        found[cid] = row
    if set(found) != set(expected):
        raise ValueError('Incomplete run: include every core, even an empty response')
    return found


def prepare(args, data):
    fresh_output(args.output)
    rows = task_rows(data, args.track)
    write_rows(args.output / 'prompts.jsonl', rows)
    field = 'proof' if args.track == 'lean' else 'response'
    write_rows(args.output / 'predictions.jsonl', [dict(core_id=r['core_id'], track=args.track,
               contract_hash=r['contract_hash'], **({'target_sha256': r['target_sha256']} if args.track == 'lean' else {}),
               **{field: ''}) for r in rows])
    meta = receipt('prepare', data, args.mode, args.model, args.agent)
    meta.update(track=args.track, task_contracts=[{k: row[k] for k in ('core_id', 'contract_hash')} for row in rows])
    write_json(args.output / 'run.json', meta)


def review_pack(args, data):
    rows = read_predictions(args.predictions, data, 'non-lean')
    fresh_output(args.output)
    review = []
    for core in data['cores']:
        review.append(dict(core_id=core['core_id'], contract_hash=core['contract_hash'],
                           response_sha256=digest(rows[core['core_id']]['response'].encode()),
                           reviewer='', criteria=[dict(criterion=c, score=None, reason='') for c in core['rubric']]))
    write_rows(args.output / 'review.jsonl', review)
    write_json(args.output / 'reviewer-packet.json', dict(predictions=rows, cores=data['cores']))
    (args.output / 'README.txt').write_text(
        'Reviewer-only packet: contains public gold candidates. Do not provide to the evaluated agent.\n'
        'For each criterion use 0 (incorrect/missing), 1 (partial), 2 (complete), with a reason and reviewer identity.\n'
        'These are human rubric judgments, not automatic correctness or admitted gold.\n', encoding='utf-8')


def assess(args, data):
    predictions = read_predictions(args.predictions, data, 'non-lean')
    reviews = [json.loads(line) for line in args.review.read_text(encoding='utf-8').splitlines() if line.strip()]
    if len(reviews) != len(data['cores']) or len({r['core_id'] for r in reviews}) != len(reviews):
        raise ValueError('One review required per core')
    cores = {c['core_id']: c for c in data['cores']}
    results = []
    for review in reviews:
        cid = review['core_id']
        if cid not in cores or review['contract_hash'] != cores[cid]['contract_hash']:
            raise ValueError('Review contract mismatch')
        response = predictions[cid]['response']
        if review['response_sha256'] != digest(response.encode()):
            raise ValueError('Review does not bind this response')
        criteria = review['criteria']
        if [c['criterion'] for c in criteria] != cores[cid]['rubric'] or not review['reviewer'].strip():
            raise ValueError('Rubric or reviewer missing')
        if any(type(c['score']) is not int or c['score'] not in (0, 1, 2) or not c['reason'].strip() for c in criteria):
            raise ValueError('Every criterion needs an integer score and reason')
        if not response.strip() and any(c['score'] for c in criteria):
            raise ValueError('Empty response cannot receive credit')
        results.append(dict(core_id=cid, family_id=cores[cid]['family_id'], review=review,
                            rubric_fraction=sum(c['score'] for c in criteria) / (2 * len(criteria))))
    fresh_output(args.output)
    write_json(args.output / 'results.json', dict(kind='expert-rubric-judgment', split='dev',
               performance_claim=False, gold_admission='pending', results=results,
               predictions_sha256=digest(args.predictions.read_bytes()), review_sha256=digest(args.review.read_bytes())))


def lean_source(cid, proof):
    target = targets()[cid]
    # This rejects common unsound placeholders and command injection. It is
    # deliberately NOT represented as a sandbox for arbitrary Lean metaprograms.
    if not proof.strip():
        raise ValueError('Empty proof')
    if re.search(r'\b(sorry|admit|axiom|unsafe|run_tac|run_elab|initialize|set_option)\b|#', proof):
        raise ValueError('Forbidden placeholder or command in proof')
    name = 'BRBSubmission.' + cid.replace('-', '_')
    source = '\n'.join('import ' + imp for imp in target['imports']) + '\nimport Lean.Util.FoldConsts\n'
    source += f'theorem {name} {target["signature"]} := (\n{proof}\n)\n#print axioms {name}\n'
    source += f'''run_cmd do
  let info ← Lean.getConstInfo `{name}
  let ty := info.type.getUsedConstantsAsSet.toList.map (·.toString)
  let vl := info.value?.map (fun v => v.getUsedConstantsAsSet.toList.map (·.toString)) |>.getD []
  let j := Lean.Json.mkObj [("type_constants", Lean.toJson ty), ("value_constants", Lean.toJson vl)]
  Lean.logInfo m!"BRB_DEPENDENCIES {{j.compress}}"
'''
    return source, name


def parse_lean_result(stdout, name):
    matches = re.findall(re.escape("'" + name + "' depends on axioms: [") + r'([^\]]*)\]', stdout)
    empty = f"'{name}' does not depend on any axioms" in stdout
    if len(matches) + int(empty) != 1:
        raise ValueError('Missing or ambiguous axiom receipt')
    axioms = sorted(a.strip() for a in matches[0].split(',') if a.strip()) if matches else []
    if set(axioms) - ALLOWED_AXIOMS:
        raise ValueError('Unapproved axiom closure: ' + ', '.join(axioms))
    deps = re.findall(r'^.*?BRB_DEPENDENCIES (\{[^\r\n]*\})\s*$', stdout, re.M)
    if len(deps) != 1:
        raise ValueError('Missing or ambiguous proof dependency receipt')
    dependencies = json.loads(deps[0])
    if set(dependencies) != {'type_constants', 'value_constants'} or any(
        not isinstance(value, list) or any(not isinstance(name, str) for name in value)
        for value in dependencies.values()
    ):
        raise ValueError('Invalid dependency receipt')
    return axioms, {key: sorted(set(value)) for key, value in dependencies.items()}


def check_environment(library, data):
    for filename in ('lean-toolchain', 'lake-manifest.json'):
        if (library / filename).read_bytes().replace(b'\r\n', b'\n') != (ROOT / filename).read_bytes().replace(b'\r\n', b'\n'):
            raise ValueError('Incompatible environment: ' + filename)
    for core in data['cores']:
        # Compare Git bytes to avoid platform newline transformations; compilation
        # artifacts are a trusted prebuilt environment, never certified by this hash.
        if digest((library / core['source_file']).read_bytes().replace(b'\r\n', b'\n')) != core['source_sha256']:
            raise ValueError('Library source differs from frozen task: ' + core['source_file'])
    return dict(library_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=library, text=True).strip(),
                library_dirty=bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=library)),
                toolchain=(library / 'lean-toolchain').read_text().strip(),
                lake_manifest_sha256=digest((library / 'lake-manifest.json').read_bytes()),
                compiled_artifacts='Trusted prebuilt imports; run the full library gate before replay.')


def replay(args, data):
    rows = read_predictions(args.predictions, data, 'lean')
    environment = check_environment(args.library, data)
    fresh_output(args.output)
    results = []
    for cid, row in rows.items():
        result = dict(core_id=cid, family_id=next(c['family_id'] for c in data['cores'] if c['core_id'] == cid),
                      status='rejected', prediction_sha256=digest(row['proof'].encode()),
                      contract_hash=row['contract_hash'], target_sha256=digest(targets()[cid]['signature'].encode()))
        try:
            source, name = lean_source(cid, row['proof'])
            (args.output / (cid + '.lean')).write_text(source, encoding='utf-8')
            with tempfile.TemporaryDirectory(prefix='brb-') as tmp:
                task = Path(tmp) / 'Submission.lean'
                task.write_text(source, encoding='utf-8')
                run = subprocess.run(['lake', 'env', 'lean', str(task)], cwd=args.library,
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                     encoding='utf-8', errors='replace', timeout=args.timeout)
            (args.output / (cid + '.log')).write_text(run.stdout, encoding='utf-8')
            result['log_sha256'] = digest(run.stdout.encode())
            if run.returncode != 0:
                result['reason'] = 'Lean compiler rejected fixed-target proof'
            else:
                axioms, dependencies = parse_lean_result(run.stdout, name)
                result.update(status='kernel-checked', axioms=axioms, dependencies=dependencies)
        except subprocess.TimeoutExpired:
            result.update(status='timeout', reason='Per-core wall-clock timeout')
        except ValueError as error:
            result['reason'] = str(error)
        results.append(result)
    meta = receipt('trusted-local-lean-replay', data, args.mode, args.model, args.agent)
    meta.update(environment=environment, predictions_sha256=digest(args.predictions.read_bytes()),
                sandbox=False, result_scope='Fixed formal subtargets only; no NL correctness certification', results=results)
    write_json(args.output / 'results.json', meta)
    return int(any(r['status'] != 'kernel-checked' for r in results))


def canary(args, data):
    """Reference succeeds; doing nothing, wrong proof and placeholders fail."""
    fresh_output(args.output)
    meta = dict(mode='lean-assisted', model='reference-canary', agent='bundled-reference',
                library=args.library, timeout=args.timeout)
    summary = []
    for case, expected in [('reference', 0), ('empty', 1), ('wrong', 1), ('placeholder', 1)]:
        predictions = []
        for row in task_rows(data, 'lean'):
            proof = targets()[row['core_id']]['reference_proof'] if case == 'reference' else {
                'empty': '', 'wrong': 'by exact True.intro', 'placeholder': 'by sorry'}[case]
            predictions.append({k: row[k] for k in ('core_id', 'track', 'contract_hash', 'target_sha256')} | {'proof': proof})
        pred = args.output / (case + '.jsonl')
        write_rows(pred, predictions)
        code = replay(argparse.Namespace(**meta, predictions=pred, output=args.output / case), data)
        if code != expected:
            raise ValueError('Canary unexpected result: ' + case)
        summary.append(dict(case=case, expected_exit=expected, actual_exit=code))
    write_json(args.output / 'canary.json', dict(kind='harness-self-test-not-model-performance', cases=summary))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ('prepare', 'review-pack', 'assess', 'replay', 'canary'):
        p = sub.add_parser(name)
        p.add_argument('--output', type=Path, required=True, help='New directory; existing output is never overwritten')
        if name in ('prepare', 'replay'):
            p.add_argument('--mode', choices=MODES, required=True)
            p.add_argument('--model', required=True)
            p.add_argument('--agent', required=True)
        if name == 'prepare':
            p.add_argument('--track', choices=('non-lean', 'lean'), required=True)
        elif name != 'canary':
            p.add_argument('--predictions', type=Path, required=True)
        if name == 'assess':
            p.add_argument('--review', type=Path, required=True)
        if name in ('replay', 'canary'):
            p.add_argument('--library', type=Path, required=True)
            p.add_argument('--timeout', type=int, default=120)
            p.add_argument('--trusted-local', action='store_true', required=True,
                           help='Acknowledge code execution: trusted proofs only, no security sandbox')
    args = parser.parse_args()
    data = registry.load()
    if args.command == 'replay':
        return replay(args, data)
    if args.command == 'canary':
        canary(args, data)
        return 0
    {'prepare': prepare, 'review-pack': review_pack, 'assess': assess}[args.command](args, data)
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, FileExistsError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(2)
