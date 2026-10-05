"""Separate projection and one-step parameters from cumulative OGD contracts."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
p=Path('website/content/readings.json');before=p.read_bytes()
snapshot=run/'leaves/pre-reader-precision-readings-v2.json'
assert not snapshot.exists();snapshot.write_bytes(before)
x=json.loads(before);r=next(r for r in x['readings'] if r['slug']=='online-ogd')
prop,lemma=r['source_theorems'][:2]
prop['contract'].update(model='Projection onto a nonempty closed convex set in real Euclidean space; Lean supports complete real Hilbert spaces.',
    parameters='Arbitrary ambient point z and feasible comparator u; no loss, learning rate or horizon.',
    regret='Pointwise comparison of distances; no regret functional.')
lemma['contract']['assumptions']='Nonempty closed convex V, feasible x and u, eta>0. '+r['notation'][3]['meaning']
lemma['contract']['parameters']='A single current loss, current feasible point x, feasible comparator u and positive step eta; x_next is the same actual projected update.'
lemma['contract']['regret']='One-round loss difference and its gradient linearization; no cumulative horizon premise.'
with p.open('w',encoding='utf-8',newline='\n') as f:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
record=dict(status='authored-for-final-review',path=p.as_posix(),prior_snapshot=snapshot.as_posix(),
    before_sha256=hashlib.sha256(before).hexdigest(),after_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
    changes='Pure Proposition2.11 distance parameters and single-round Lemma2.12 parameters, removing irrelevant inherited regret/horizon/tuning fields.',
    statement_change=False,proof_change=False,source_body_review_raw_preserved=True)
with (run/'reader-precision-v2.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(record,f,indent=2);f.write('\n')
print('Reader projection and one-step contract parameters precisely separated.')
