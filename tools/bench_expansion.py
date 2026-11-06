#!/usr/bin/env python3
"""Draft-package replay and exports. Trusted local inputs only; no sandbox or judge."""
from __future__ import annotations

import argparse
import hashlib
import json
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import bench_task_contract as intake
from tools.banditrlbench import parse_lean_result

BENCH = ROOT / 'benchmarks/banditrlbench'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def file_hash(path):
    return digest(path.read_bytes().replace(b'\r\n', b'\n'))

def read(path):
    return json.loads(path.read_text(encoding='utf-8'))

def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n', encoding='utf-8', newline='\n')

def package(identity):
    if not re.fullmatch(r'BRB-[A-Z]+-[KRL]', identity):
        raise ValueError('Unknown package ID')
    p = BENCH / 'tasks' / identity
    task = intake.validate(p)
    env = read(p/'environment/manifest.json')
    for name, expected in env.get('contract_files_sha256', {}).items():
        if file_hash(p/name) != expected:
            raise ValueError('Changed contract file: '+name)
    if not env.get('contract_files_sha256'):
        raise ValueError('Missing auxiliary file seals')
    return p, task, env

def source_for(target, proof, name):
    if not proof.strip():
        raise ValueError('Empty proof')
    # A diagnostic filter, NOT a Lean metaprogram sandbox.
    if re.search(r'\b(sorry|admit|axiom|unsafe|run_tac|run_elab|run_cmd|initialize|set_option|import|theorem|def|namespace|end)\b|#', proof):
        raise ValueError('Forbidden placeholder or command in proof expression')
    source = '\n'.join('import '+i for i in target['imports'])+'\nimport Lean.Util.FoldConsts\n'
    source += f'theorem {name} {target["signature"]} := (\n{proof}\n)\n#print axioms {name}\n'
    source += f'''run_cmd do
  let info ← Lean.getConstInfo `{name}
  let ty := info.type.getUsedConstantsAsSet.toList.map (·.toString)
  let vl := info.value?.map (fun v => v.getUsedConstantsAsSet.toList.map (·.toString)) |>.getD []
  let j := Lean.Json.mkObj [("type_constants", Lean.toJson ty), ("value_constants", Lean.toJson vl)]
  Lean.logInfo m!"BRB_DEPENDENCIES {{j.compress}}"
'''
    return source

def lean_check(p, proof, library, out, label, timeout=600, target=None):
    expected = read(p/'environment/workspace/target.json')
    target = expected if target is None else target
    result = dict(control=label, status='fail', prediction_sha256=digest(proof.encode()),
                  target_sha256=file_hash(p/'environment/workspace/target.json'), evidence_scope='trusted-local')
    try:
        if target != expected:
            raise ValueError('Fixed target/import mismatch')
        name = 'BenchExpansion.'+p.name.replace('-','_')
        source = source_for(target, proof, name)
        path = out/(label+'.lean')
        path.write_text(source, encoding='utf-8', newline='\n')
        result['source_sha256'] = file_hash(path)
        cmd = ['lake','env','lean',str(path.resolve())]
        result['command'] = ['lake','env','lean',f'<output>/{label}.lean']
        result['timeout_seconds'] = timeout
        start=time.monotonic()
        try:
            run = subprocess.run(cmd,cwd=library,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                                 encoding='utf-8',errors='replace',timeout=timeout)
            log=run.stdout
            result['exit_code']=run.returncode
            if run.returncode == 0:
                axioms,deps=parse_lean_result(log,name)
                result.update(status='pass',axioms=axioms,dependencies=deps)
            else:
                result['reason']='Lean rejected the fixed target'
        except subprocess.TimeoutExpired as e:
            log=e.stdout or b''
            if isinstance(log,bytes): log=log.decode('utf-8',errors='replace')
            result.update(reason='Compiler wall-clock timeout; process-tree isolation not established',timeout=True)
        finally:
            result['elapsed_seconds']=round(time.monotonic()-start,6)
        (out/(label+'.log')).write_text(log,encoding='utf-8',newline='\n')
        result['log_sha256']=digest(log.encode())
    except ValueError as e:
        result['reason']=str(e)
    return result

def nl_check(p, label, response, review_path=None):
    review_path = review_path or p/'tests/review.json'
    reviews=read(review_path)
    rubric=read(p/'tests/rubric.json')
    row=reviews['controls'][label]
    if reviews['rubric_sha256'] != file_hash(p/'tests/rubric.json'):
        raise ValueError('Stale rubric review')
    if row['response_sha256'] != digest(response.encode()):
        raise ValueError('Stale response review')
    if reviews['reviewer'] in ('','Codex /root'):
        raise ValueError('Distinct reviewer required')
    if [x['id'] for x in row['criteria']] != [x['id'] for x in rubric['criteria']]:
        raise ValueError('Incomplete criterion review')
    axes={}
    for spec,r in zip(rubric['criteria'],row['criteria']):
        if type(r['score']) is not int or r['score'] not in (0,1,2) or not r['reason'].strip():
            raise ValueError('Score and justification required')
        if not response.strip() and r['score']:
            raise ValueError('Empty response cannot receive credit')
        axes.setdefault(spec['axis'],dict(earned=0,possible=0))
        axes[spec['axis']]['earned']+=r['score']
        axes[spec['axis']]['possible']+=2
    return dict(control=label,status='pass' if all(r['score']==2 for r in row['criteria']) else 'fail',
                prediction_sha256=digest(response.encode()),axes=axes,reviewer=reviews['reviewer'],
                assessment='recorded independent agent rubric judgment; human expert admission pending',
                review_sha256=file_hash(review_path))

def environment_receipt(library,env):
    for name,expected in env['library_source_hashes'].items():
        if file_hash(library/name)!=expected:
            raise ValueError('Pinned source mismatch: '+name)
    if file_hash(library/'lake-manifest.json')!=env['dependency_lock_sha256']:
        raise ValueError('Dependency lock mismatch')
    if (library/'lean-toolchain').read_text().strip()!=env['toolchain']:
        raise ValueError('Toolchain mismatch')
    # The full build gate is recorded separately; artifacts are trusted inputs.
    return dict(pinned_library_commit=env['library_commit'],
        checkout_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=library,text=True).strip(),
        checkout_dirty=bool(subprocess.check_output(['git','status','--porcelain'],cwd=library)),
        python=platform.python_version(),python_executable_sha256=digest(Path(sys.executable).read_bytes()),
        platform=platform.platform(),toolchain=env['toolchain'],dependency_lock_sha256=env['dependency_lock_sha256'],
        lean_version=subprocess.check_output(['lake','env','lean','--version'],cwd=library,text=True).strip(),
        runner_sha256=file_hash(Path(__file__)),sandbox=False,harbor_executed=False,
        access_enforcement='Operator-declared only; no isolated model run',
        resource_enforcement='Per compiler wall-clock timeout only; CPU/memory/process-tree caps pending')

def controls(args):
    p,task,env=package(args.task)
    args.output.mkdir(parents=True,exist_ok=False)
    rows=[]
    lean=task['answer_format']=='lean'
    environment=environment_receipt(args.library,env)
    for label in ('reference','no-op','wrong-answer','placeholder'):
        name=('solution/proof.txt' if lean else 'solution/reference.txt') if label=='reference' else 'tests/controls/'+label+'.txt'
        response=(p/name).read_text(encoding='utf-8')
        row=lean_check(p,response,args.library,args.output,label) if lean else nl_check(p,label,response)
        row['expected']='pass' if label=='reference' else 'fail'
        if lean:
            row.update(assessment='fixed-target kernel control only',
                       agentic_rubric={'c1':'pass' if row['status']=='pass' else 'fail',
                                       'c2':'unassessed; independent trajectory review required'})
        rows.append(row)
    if lean:
        proof=(p/'solution/proof.txt').read_text(encoding='utf-8')
        for label,key,value in [('statement-mutation','signature',': True'),('import-mutation','imports',['Mathlib'])]:
            target=read(p/'environment/workspace/target.json');target[key]=value
            rows.append(lean_check(p,proof,args.library,args.output,label,target=target))
        rows.append(lean_check(p,'by\n  axiom forged : False\n  exact False.elim forged',args.library,args.output,'axiom-injection'))
        rows.append(lean_check(p,'by\n  exact True.intro\n#print axioms forged',args.library,args.output,'output-spoofing'))
        rows.append(lean_check(p,proof,args.library,args.output,'timeout',timeout=0.001))
        with tempfile.TemporaryDirectory(prefix='bench-contract-') as tmp:
            copy=Path(tmp)/p.name
            shutil.copytree(p,copy)
            (copy/'tests/contract.json').write_text('{}\n')
            try: intake.validate(copy); status='pass'
            except (ValueError,KeyError): status='fail'
            rows.append(dict(control='verifier-tampering',status=status,reason='Modified verifier contract rejected by intake seal',evidence_scope='contract preflight; not runtime sandbox tamper resistance'))
        with tempfile.TemporaryDirectory(prefix='bench-visible-') as tmp:
            visible=Path(tmp)
            shutil.copy2(p/'instruction.md',visible/'instruction.md')
            shutil.copytree(p/'environment/workspace',visible/'environment/workspace')
            names=sorted(x.relative_to(visible).as_posix() for x in visible.rglob('*') if x.is_file())
            leaked=[n for n in names if n.startswith(('solution/','tests/'))]
            rows.append(dict(control='solution-leakage',status='fail' if not leaked else 'pass',
                reason='Exposure probe found no solution/test files in staged visible inputs',visible_files=names,
                evidence_scope='staging inventory only; no access-enforced isolation, image-layer or adversarial probe'))
        for r in rows: r.setdefault('expected','fail')
    ok=all(r['status']==r['expected'] for r in rows)
    report=dict(task=task['id'],family=task['family'],ability=task['ability'],access=task['access'],split='dev',
                contract_sha256=task['contract_sha256'],environment=environment,controls=rows,
                all_expected=ok,performance_claim=False,agentic_completion=False,
                scope='Reference/control development evidence only; no system score, independent human admission, isolated agent or Harbor run.')
    write(args.output/'results.json',report)
    print(json.dumps(dict(task=task['id'],controls=len(rows),all_expected=ok)))
    return 0 if ok else 1

def verify(args):
    p,task,env=package(args.task)
    args.output.mkdir(parents=True,exist_ok=False)
    response=args.answer.read_text(encoding='utf-8')
    if task['answer_format']=='lean':
        environment=environment_receipt(args.library,env)
        result=lean_check(p,response,args.library,args.output,'submission')
        trajectory=[] if args.trajectory is None else [json.loads(x) for x in args.trajectory.read_text(encoding='utf-8').splitlines() if x.strip()]
        result.update(trajectory_sha256=None if args.trajectory is None else file_hash(args.trajectory),
                      trajectory_events=len(trajectory),trajectory_review='pending independent authenticity and coverage review',
                      agentic_completion=False,environment=environment)
    else:
        if args.review is None: raise ValueError('Natural-language verification requires an independent response-bound rubric review')
        result=nl_check(p,'submission',response,args.review)
    write(args.output/'result.json',dict(task=task['id'],family=task['family'],ability=task['ability'],access=task['access'],
        split='dev',contract_sha256=task['contract_sha256'],result=result,admission='not-granted',performance_claim=False))
    return 0 if result['status']=='pass' else 1

def export(args):
    manifest=read(BENCH/'expansion/families.json')
    if args.split!='dev':
        raise ValueError('Only public dev exists; held-out access is not implemented')
    rows=[]
    for family in manifest['families']:
        for identity in family['task_ids']:
            p,task,env=package(identity)
            row=dict(task_id=identity,family=task['family'],split=task['split'],ability=task['ability'],access=task['access'],
                     stage=task['stage'],contract_sha256=task['contract_sha256'],instruction=(p/'instruction.md').read_text(encoding='utf-8'),
                     workspace={x.relative_to(p/'environment/workspace').as_posix():x.read_text(encoding='utf-8') for x in (p/'environment/workspace').rglob('*') if x.is_file()})
            if args.include_solutions:
                row['training_solution']=(p/('solution/proof.txt' if task['answer_format']=='lean' else 'solution/reference.txt')).read_text(encoding='utf-8')
            rows.append(row)
    args.output.mkdir(parents=True,exist_ok=False)
    name='training-with-solutions.jsonl' if args.include_solutions else 'prompts.jsonl'
    (args.output/name).write_text(''.join(json.dumps(x,ensure_ascii=False)+'\n' for x in rows),encoding='utf-8',newline='\n')
    write(args.output/'manifest.json',dict(version=manifest['version'],kind='opt-in-training' if args.include_solutions else 'prompt-only',families=len(manifest['families']),tasks=len(rows),split='dev',held_out=False,admission='not-granted',file_sha256=file_hash(args.output/name)))
    return 0

def main():
    p=argparse.ArgumentParser(description=__doc__);s=p.add_subparsers(dest='cmd',required=True)
    c=s.add_parser('controls');c.add_argument('--task',required=True);c.add_argument('--library',type=Path,default=ROOT);c.add_argument('--output',type=Path,required=True);c.add_argument('--trusted-local',action='store_true',required=True)
    v=s.add_parser('verify');v.add_argument('--task',required=True);v.add_argument('--answer',type=Path,required=True);v.add_argument('--review',type=Path);v.add_argument('--trajectory',type=Path);v.add_argument('--library',type=Path,default=ROOT);v.add_argument('--output',type=Path,required=True);v.add_argument('--trusted-local',action='store_true',required=True)
    e=s.add_parser('export');e.add_argument('--output',type=Path,required=True);e.add_argument('--split',choices=['dev'],default='dev');e.add_argument('--include-solutions',action='store_true')
    a=p.parse_args()
    return {'controls':controls,'verify':verify,'export':export}[a.cmd](a)

if __name__=='__main__':
    raise SystemExit(main())
