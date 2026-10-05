"""Freeze bounded anti-anchored review inputs for the three retained headers."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
    p=run/n;assert not p.exists(),p
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
for label in ['retained-module-types-v1-01','actual-public-types-v1-01','actual-scoped-graph-v1-01']:
    assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v1.json')
for p,h in dict(freeze['module'],**freeze['canary']).items():assert sha(p)==h,p
blind=load(run/'blind-receipt-v1.json')
assert sha(run/'blind-packet-v1.md') in json.dumps(blind) and sha(run/'blind-reconstruction-v1.md') in json.dumps(blind)
graph=load('tmp/online-first-order-migration-scoped-graph-v1.json')
assert {n['name'].rsplit('.',1)[-1] for n in graph['nodes']}==set(freeze['headers'])
pairs=[]
for e in graph['edges']:
    if e['target'].startswith('BanditRL.OnlineConvex.') and (e['kind']=='value' or e['also_in_value']):pairs.append([e['source'],e['target']])
for target in ['finitePart_eventually','convex_gradient_lower_bound','convexExtended_iff_toReal']:
    assert ['BanditRL.OnlineConvex.theorem_2_7','BanditRL.OnlineConvex.'+target] in pairs
write('ready-dependencies-v1.json',dict(status='actual-compiled-scoped-ready',graph_path='tmp/online-first-order-migration-scoped-graph-v1.json',graph_sha256=sha('tmp/online-first-order-migration-scoped-graph-v1.json'),
    scope_nodes=len(graph['nodes']),actual_edges=len(graph['edges']),project_proof_pairs=pairs,new_export=True,
    full_graph_export=False,canary_graph_export=False,existing_retained_bodies=True,package_accepted=False))
p=run/'compiled-scoped-graph-v1.json';p.write_bytes(Path('tmp/online-first-order-migration-scoped-graph-v1.json').read_bytes())
write('source-review-packet-v1.md','''Distinct source CONTRACT review, requested GPT-6 Astra / medium. Independently rehash every contract-source-inputs-v1.json row. Seek mismatch rather than confirm root. Three retained actual headers/scoped context, one source Theorem2.7 and two explicit helpers; ZERO new proof/registry nodes. Source Orabona v10 printed11/PDF23 (PDF22 contextual definitions). Every y in Rd, including top outside effective domain; f globally noBottom, convex, x interior domf, differentiable at x. Complete real Hilbert-space generality includes Euclidean instances. No global differentiability/closed/bounded/finite-comparator or full-domain assumption added.

Actual source derivative uses canonical f.toReal at interior x. The first helper proves its embedding agrees with f on a neighborhood under interior/noBottom; infinite values elsewhere are NOT globally treated as zero. Inspect actual pinned toReal/gradient definitions and canonical derivative meaning. The real ConvexOn helper has only convexity on V, x/y membership and DifferentiableAt at x, no open-set assumption; it is a stronger generalized algebraic/analytic helper, not another printed theorem. Scope retains gradient at interior point/all-y inequality and separately top comparator case. Pinned APIs and actual public types/three native draft fences retrieved. Original historical same-model reviews are not distinct actor acceptance.

Actual three-proof module and current compiled environment graph present for context/readiness; contract verdict now, separate retained-body/canary/axiom/guard/integrated/reader gates follow. Graph is scoped3 public proof values/direct boundary only, NOT full project/canary export. Existing canary loss x if x>0 else top gives nonconstant finite1/2, nonzero derivative/gradient1, open(0,infinity) domain and outside y=-1/top. Fresh canary replay still pending. Current readers are supplied for required qualification audit; do not certify them unchanged automatically. One lower reuse route, no statement/code weakening.

Return accepted|rejected|accepted-with-explicit-delta, target_verdicts for all three qualified names, seven-slot differences per target and canonical finite-part local semantics, mathematical_repairs and required_reader_corrections separately. Write ONLY source-contract-review-v1.md/source-contract-receipt-v1.json here, actor.task=/root/source_reviewer, reviewed_files rawSHA, report path/SHA. Contract only, not body/package/chapter/Goal/main/live acceptance. Distinct automated actors with prior history; no human/external/runtime-model attestation. Earlier accepted finite-loss/convex/FTL/OGD artifacts immutable. Whole Chapters1-16 Goal active, Chapter2 totalnull/19 legacy migrations pending, no Chapter3 proof writing.''')
paths={p.as_posix() for p in run.rglob('*') if p.is_file()}
paths.update(p.as_posix() for p in Path('docs/contracts/online-first-order-migration-v1').rglob('*') if p.is_file())
paths.update(p.as_posix() for p in Path('docs/contracts/online-first-order-v1').rglob('*') if p.is_file())
paths.update(['BanditRLProof/OnlineConvexFirstOrder.lean','Tests/OnlineConvexFirstOrderCanary.lean','BanditRLProof/OnlineConvexExtended.lean',
    '../research-online-ogd/tmp/pdfs/orabona-v10.pdf','tmp/online-first-order-migration-scoped-graph-v1.json',
    '.lake/packages/mathlib/Mathlib/Analysis/Convex/Deriv.lean','.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean',
    '.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean','.agents/skills/bandit-semantic-roundtrip/SKILL.md',
    'website/content/readings.json','website/content/highlights.json','website/content/chapters.json','lean-toolchain','lakefile.lean','lake-manifest.json',
    'tasks/ONLINE-FIRST-ORDER-MIGRATION-20261005.md','conversion-windows/ONLINE-FIRST-ORDER-MIGRATION-20261005.md','proof-obligations/ONLINE-FIRST-ORDER-MIGRATION-20261005.md',
    'runs/online-finite-loss-20261005/accepted-decision-v1.json','runs/online-finite-loss-20261005/native-acceptance-overlay-v2.json'])
write('contract-source-inputs-v1.json',dict(scope='three retained first-order contracts only',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Source contract fixed inputs:',len(paths),'actual scoped edges',len(graph['edges']),'; proving review pending.')
