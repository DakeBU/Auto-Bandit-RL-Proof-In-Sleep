#!/usr/bin/env python3
"""Capture an honest search/query/reference replay; not an evaluated agent run."""
import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--task',choices=['BRB-IW-L','BRB-BE-L'],required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False)
    task=ROOT/'benchmarks/banditrlbench/tasks'/a.task
    if a.task=='BRB-IW-L':
        paths=['BanditRLProof/Exp3ImportanceWeighted.lean','BanditRLProof/Exp3ComparatorBernstein.lean']
        pattern='sum_prob_mul|importanceWeightedLoss'
        queries=['BanditRLProof.Exp3.sum_prob_mul_importanceWeightedLoss_eq_loss','Finset.sum_eq_single','Finset.sum_add_distrib','Finset.sum_sub_distrib','Finset.mul_sum']
    else:
        paths=['BanditRLProof/RL/FiniteHorizonPolicy.lean','BanditRLProof/RL/FiniteHorizonOptimality.lean']
        pattern='valueAt|decreasingInduction'
        queries=['BanditRLProof.FiniteHorizonRL.MarkovPolicy.valueAt_bellman','BanditRLProof.FiniteHorizonRL.MarkovPolicy.valueAt_horizon','Nat.decreasingInduction']
    target=json.loads((task/'environment/workspace/target.json').read_text(encoding='utf-8'))
    query=a.output/'Query.lean'
    query.write_text('\n'.join('import '+x for x in target['imports'])+'\n'+'\n'.join('#check '+x for x in queries)+'\n',encoding='utf-8',newline='\n')
    commands=[('search',['rg','-n',pattern,*paths]),('lean-query',['lake','env','lean',str(query.resolve())]),
              ('reference-replay',[sys.executable,'tools/bench_expansion.py','verify','--task',a.task,'--answer',str(task/'solution/proof.txt'),'--library','.', '--output',str((a.output/'verification').resolve()),'--trusted-local'])]
    events=[]
    for seq,(kind,cmd) in enumerate(commands,1):
        start=time.monotonic()
        r=subprocess.run(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,encoding='utf-8',errors='replace',timeout=600)
        log=a.output/f'{seq:02d}-{kind}.log';log.write_text(r.stdout,encoding='utf-8',newline='\n')
        # Public command uses path placeholders; the guide defines their exact mapping.
        public=[str(x).replace(str(ROOT),'<repo>').replace(str(a.output.resolve()),'<output>').replace(sys.executable,'python') for x in cmd]
        events.append(dict(sequence=seq,kind=kind,command=public,exit_code=r.returncode,elapsed_seconds=round(time.monotonic()-start,6),stdout_file=log.name,stdout_sha256=hashlib.sha256(r.stdout.encode()).hexdigest()))
        if r.returncode: break
    (a.output/'trajectory.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in events),encoding='utf-8',newline='\n')
    (a.output/'scope.json').write_text(json.dumps(dict(task=a.task,actor='Codex /root reference operator',model_trial=False,isolated=False,harbor=False,
        capture_scope='Commands actually executed by this tool: search, Lean queries and preauthored reference replay. Author proof-construction history before this tool is not reconstructed. This is not a blind agent solution trajectory.',
        target_sha256=hashlib.sha256((task/'environment/workspace/target.json').read_bytes()).hexdigest(),proof_sha256=hashlib.sha256((task/'solution/proof.txt').read_bytes()).hexdigest(),
        command_path_mapping={'<repo>':'repository checkout root','<output>':'--output directory','python':'invoking Python executable; version/hash in verification/result.json'},
        tool_sha256=hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()),indent=2)+'\n',encoding='utf-8',newline='\n')
    return int(any(x['exit_code'] for x in events))

if __name__=='__main__':raise SystemExit(main())
