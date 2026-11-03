"""Small source-bound benchmark registry, prompt exporter and reader projection."""
from __future__ import annotations
import argparse
import hashlib
import html
import json
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
        if solutions:
            row.update(answer=core['answer'],rubric=core['rubric'])
        rows.append(row)
    return rows

def build_pages(output, verified, generated_at, layout, write_page):
    data=load(); escape=html.escape
    def emit(path,title,body):
        write_page(output,path,layout(path,title,body,[], 'banditrlbench',verified,generated_at))
    intro='<div class="callout warning">Development seed: public dev examples, pending independent mathematical admission. No hidden test set, measured model baseline or whole-library coverage.</div>'
    nav='<p><a href="../index.html">Benchmark overview</a> · <a href="../non-lean/index.html">Without Lean</a> · <a href="../lean/index.html">Lean companion</a></p>'
    cards=''.join(f'<article class="info-card"><h3>{title}</h3><p>{text}</p><a href="{path}/index.html">Open track →</a></article>' for title,text,path in [('Without Lean','Explain guarantees, identify assumptions and find invalid inferences. No Lean installation required.','non-lean'),('Lean companion','Read and apply exact formal statements. Two authored library-application references; compilation evidence is recorded separately.','lean')])
    overview=f'<section class="hero"><p class="eyebrow">BanditRLBench · {data["version"]}</p><h1 class="page-title">Reason about sequential learning</h1><p class="lede">Source-bound questions for training and evaluating bandit and reinforcement-learning knowledge and mathematical reasoning.</p></section>{intro}<section><h2>Two ways to work</h2><div class="card-grid">{cards}</div></section><section><h2>First checkpoint</h2><p>Four mathematical cores, four natural-language views and two bounded Lean companions. Views share core identities and development splits; they are not six distinct problems. This first batch covers regret accounting, expectation, confidence budgets and estimator semantics. Reinforcement-learning questions and broader graph coverage are future work.</p><p><a href="cores.json">Download source-bound registry and public solutions</a> · <a href="Reference.lean">Lean reference file</a> · <a href="https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/tree/{data["source_commit"]}">Library snapshot</a></p></section><section><h2>Contribute and evaluate</h2><p>Use the rubric for explicit mathematical assessment. Closed-book, text-retrieval, graph-retrieval and Lean-assisted runs must be reported separately. A compiled reference does not mean a model prediction was tested. No substring grader or measured model score is provided.</p><p><a href="https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/tree/feat/banditrlbench-seed-20261103/benchmarks/banditrlbench">Repository guide and contribution tracks</a></p></section>'
    emit('banditrlbench/index.html','BanditRLBench',overview)
    for track,title in [('non-lean','Without Lean'),('lean','Lean companion')]:
        selected=[c for c in data['cores'] if track=='non-lean' or c['lean']['reference_status']!='planned']
        listing=''
        for core in selected:
            question=core['question'] if track=='non-lean' else core['lean']['question']
            source=f'https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/{core["source_commit"]}/{core["source_file"]}'
            limitations=('This formal reference proves the listed subtarget only. It does not certify the full natural-language answer or a submitted model proof.' if track=='lean' else 'Natural-language answer: development candidate, not independently admitted gold.')
            listing+=f'<article class="info-card" id="{core["core_id"]}"><p class="eyebrow">{core["core_id"]} · public dev · {escape(core["family_id"])}</p><h2>{escape(core["title"])}</h2><h3>Assumptions</h3><ul>'+''.join('<li>'+escape(a)+'</li>' for a in core['assumptions'])+f'</ul><p>{escape(question)}</p><details><summary>Solution and assessment rubric</summary><p>{escape(core["answer"])}</p><ol>'+''.join('<li>'+escape(a)+'</li>' for a in core['rubric'])+f'</ol><p>{escape(limitations)}</p></details><details><summary>Source, graph and verification boundary</summary><p><a href="{source}" data-benchmark-core="{core["core_id"]}" data-benchmark-contract="{core["contract_hash"]}" data-benchmark-snapshot="{core["source_commit"]}">Frozen benchmark source ({core["source_commit"][:7]})</a> · <code>{escape(core["source_declaration"])}</code></p><p>{escape(core["graph_evidence"])}</p><p>Contract: <code>{core["contract_hash"]}</code>. NL review: {escape(core["nl_review"])}.</p>'+('<p><a href="../Reference.lean">Reference proof and axiom commands</a>. Reference status: '+escape(core['lean']['reference_status'])+'. See repository verification receipt for the actual compiler environment.</p>' if track=='lean' else '')+'</details></article>'
        emit(f'banditrlbench/{track}/index.html','BanditRLBench · '+title,f'<section class="hero"><p class="eyebrow">BanditRLBench</p><h1 class="page-title">{title}</h1></section>'+nav+intro+listing)
    destination=output/'banditrlbench'
    (destination/'cores.json').write_bytes(DATA.read_bytes())
    (destination/'Reference.lean').write_bytes((ROOT/'benchmarks/banditrlbench/lean/Reference.lean').read_bytes())

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
