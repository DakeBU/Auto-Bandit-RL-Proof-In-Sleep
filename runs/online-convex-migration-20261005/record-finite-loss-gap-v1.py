"""Keep the newly detected main-text finite-loss consequence mandatory."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
r=load(run/'public-body-receipt-v1.json');assert r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert hashlib.sha256(Path(r['report']).read_bytes()).hexdigest()==r['report_sha256']
gap=dict(status='mandatory-pending-new-contract',source='Orabona v10 printed9-10/PDF21-22 finite-loss constraint sentence',
    proposed_precise_terminal='effectiveDomain (fun x => f x + extendedIndicator V x) = effectiveDomain f ∩ V under ∀ x, f x ≠ bottom',
    source_semantics='Finite constrained loss requires x in V AND f(x) finite; membership alone does not suffice when f(x)=top.',
    dependency='Actual indicator-addition proof contains supporting epigraph identity, but no separate frozen/public domain-intersection endpoint is present in this22-proof package.',
    contract_stabilized=False,public_proof_present=False,chapter_obligation=True,required_before_unnumbered_group_closed=True,
    review_receipt=(run/'public-body-receipt-v1.json').as_posix(),review_report_sha256=r['report_sha256'],chapter_complete=False,whole_goal='active')
write(run/'finite-loss-constraint-gap-v1.json',gap)
p=Path('website/content/chapters.json');x=load(p);c=next(c for c in x['chapters'] if c['slug']=='online-convex')
c['completion_definition']='Definitions2.2-2.3, Theorem2.4 with explicit noBottom/convex effective domain/strict weights, named domain convexity/indicator equivalence/indicator-addition convexity, and mandatory Examples2.5/2.6. Eight and three retained proofs respectively; no new proof code. The separate finite-loss/domain-intersection consequence remains required. This is not completion of all Chapter 2.'
c['completion_blockers'].append('Finite constrained loss iff x in V and f(x) finite: separate source-frozen public domain-intersection endpoint remains required; membership alone is insufficient if f(x)=top.')
write(p,x)
p=Path('website/content/readings.json');x=load(p);r=next(c for c in x['readings'] if c['slug']=='online-convex')
r['source_theorems'][1]['local_status']['boundary']='Named indicator-domain, indicator-convexity and indicator-addition-convexity endpoints only. The separate finite-loss/domain-of-sum intersection endpoint remains required; x in V alone does not ensure finite f. Four closure constructions have retained shared implementations with separately recorded migration acceptance. Chapter2 and whole-book acceptance remain incomplete.'
write(p,x)
p=Path('research-wiki/contribution-contracts/ONLINE-CONVEX-MIGRATION-20261005.json');x=load(p)
x['truth_boundary']+=' The separately detected finite-loss/domain-of-sum intersection consequence remains mandatory and is not accepted by these22 endpoints.'
write(p,x)
print('Mandatory finite-loss/domain-intersection gap explicitly recorded and visible; no theorem/contract target weakened or new proof claimed.')
