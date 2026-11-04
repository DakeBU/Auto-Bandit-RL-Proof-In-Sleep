"""Small source-bound benchmark registry, prompt exporter and reader projection."""
from __future__ import annotations
import argparse
import hashlib
import html
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'benchmarks/banditrlbench/cores.json'

def contract_hash(core):
    contract = {key: core[key] for key in ('assumptions','question','family_id','split','source_commit')}
    return hashlib.sha256(json.dumps(contract,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def validate(data):
    seen, families = set(), {}
    for core in data['cores']:
        if not re.fullmatch(r'[0-9a-f]{40}', core['source_commit']):
            raise ValueError('Source snapshot must be an immutable full Git commit')
        if core['core_id'] in seen or core['contract_hash'] != contract_hash(core):
            raise ValueError('Duplicate identity or changed mathematical contract')
        seen.add(core['core_id'])
        if families.setdefault(core['family_id'],core['split']) != core['split']:
            raise ValueError('Family crosses dataset splits')
        if core['split'] != 'dev' or not core['assumptions'] or not core['rubric']:
            raise ValueError('Seed requires public dev split, assumptions and rubric')
        blob = subprocess.check_output(['git','show',core['source_commit']+':'+core['source_file']],cwd=ROOT)
        if hashlib.sha256(blob).hexdigest()!=core['source_sha256']:
            raise ValueError('Source identity mismatch')
        if core['source_declaration'].split('.')[-1] not in blob.decode():
            raise ValueError('Missing source anchor')
    targets = json.loads((ROOT/'benchmarks/banditrlbench/targets.json').read_text(encoding='utf-8'))
    authored = {c['core_id'] for c in data['cores'] if c['lean']['reference_status'] != 'planned'}
    if set(targets) != authored:
        raise ValueError('Formal target set differs from authored references')
    reference = (ROOT/'benchmarks/banditrlbench/lean/Reference.lean').read_text(encoding='utf-8')
    for cid, target in targets.items():
        if hashlib.sha256(target['signature'].encode()).hexdigest() != target['target_sha256']:
            raise ValueError('Formal signature seal changed')
        matched = re.search(r'theorem '+cid.replace('-', '_')+r'\s+([\s\S]*?)\s*:=\s*by', reference)
        if matched is None or re.sub(r'\s+', '', matched[1]) != re.sub(r'\s+', '', target['signature']):
            raise ValueError('Formal signature differs from compiled reference')
    return data

def load():
    return validate(json.loads(DATA.read_text(encoding='utf-8')))

def prompts(data, track, solutions=False):
    rows=[]
    for core in data['cores']:
        if track=='lean' and core['lean']['reference_status']=='planned':
            continue
        row={key:core[key] for key in ('core_id','family_id','split','contract_hash','assumptions','source_commit')}
        row.update(track=track,question=core['question'] if track=='non-lean' else core['lean']['question'])
        if track=='lean':
            row['scope']='Formal companion covers the stated Lean subtarget; not certification of the complete NL answer.'
            target = json.loads((ROOT/'benchmarks/banditrlbench/targets.json').read_text(encoding='utf-8'))[core['core_id']]
            row.update(imports=target['imports'], target_signature=target['signature'],
                       target_sha256=hashlib.sha256(target['signature'].encode()).hexdigest())
            if solutions:
                row['reference_proof'] = target['reference_proof']
        if solutions:
            if track == 'lean':
                row.update(answer=target['reference_proof'], rubric=[
                    'The proof must elaborate against the exact sealed target signature.',
                    'Compiler acceptance and the allowed axiom closure are required; no placeholders.',
                    'Only this formal subtarget is certified, not the entire parent NL answer.'])
            else:
                row.update(answer=core['answer'],rubric=core['rubric'])
        rows.append(row)
    return rows

def build_pages(output, verified, generated_at, layout, write_page):
    try:
        from .banditrlbench_reader import build_pages as render
    except ImportError:
        from banditrlbench_reader import build_pages as render
    data = load()
    render(data, output, verified, generated_at, layout, write_page)
    for track in ('non-lean', 'lean'):
        (output / 'banditrlbench' / (track + '-prompts.jsonl')).write_text(
            ''.join(json.dumps(row, ensure_ascii=False) + '\n' for row in prompts(data, track)), encoding='utf-8')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['validate','export'])
    parser.add_argument('--track',choices=['non-lean','lean'],default='non-lean')
    parser.add_argument('--include-solutions',action='store_true')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args(); data=load()
    if args.command=='validate':
        print('Valid development seed: 4 cores, 4 NL views, 2 authored Lean references; semantic admission pending.'); return
    if args.output is None:parser.error('export requires --output')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(''.join(json.dumps(row,ensure_ascii=False)+'\n' for row in prompts(data,args.track,args.include_solutions)),encoding='utf-8')

if __name__=='__main__':main()
