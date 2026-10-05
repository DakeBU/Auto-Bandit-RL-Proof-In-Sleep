"""Freeze anti-anchored source review with actual types/APIs/proof-value readiness."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
for label in ['retained-module-types-v1-01','actual-public-types-v1-01','actual-scoped-graph-v1-01','actual-pinned-API-retrieval-v1-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v1.json')
for p,h in dict(freeze['module'],**freeze['canary']).items():assert sha(p)==h,p
blind=load(run/'blind-receipt-v1.json')
assert sha(run/'blind-packet-v1.md') in json.dumps(blind) and sha(run/'blind-reconstruction-v1.md') in json.dumps(blind)
graph_path='tmp/online-optimality-migration-scoped-graph-v1.json';graph=load(graph_path)
assert graph['root_module']=='BanditRLProof' and graph['extraction']['source']=='compiled-environment'
assert {n['name'].rsplit('.',1)[-1] for n in graph['nodes']}==set(freeze['headers']) and all(n['has_value'] for n in graph['nodes'])
pairs=[]
for e in graph['edges']:
 if e['target'].startswith('BanditRL.OnlineConvex.') and (e['kind']=='value' or e['also_in_value']):pairs.append([e['source'],e['target']])
required=[['minOn_real_iff_gradient','convex_gradient_lower_bound'],['theorem_2_8','minOn_finitePart_iff'],['theorem_2_8','minOn_real_iff_gradient'],['interior_min_iff_gradient_zero','minOn_finitePart_iff'],['interior_min_iff_gradient_zero','theorem_2_8']]
for a,b in required:assert ['BanditRL.OnlineConvex.'+a,'BanditRL.OnlineConvex.'+b] in pairs
write('ready-dependencies-v1.json',dict(status='actual-compiled-scoped-ready',graph_path=graph_path,graph_sha256=sha(graph_path),scope_nodes=len(graph['nodes']),actual_edges=len(graph['edges']),project_proof_pairs=pairs,new_export=True,full_graph_export=False,canary_graph_export=False,existing_retained_bodies=True,package_accepted=False))
(run/'compiled-scoped-graph-v1.json').write_bytes(Path(graph_path).read_bytes())
write('source-review-packet-v1.md','''Required distinct source CONTRACT review, GPT-6 Astra / medium. Rehash every contract-source-inputs-v1.json row and actual4nativeheaders/scopedcontext, freshsourcev10p11PDF23, neutraldecoder, pinnedimports/APIs. Seek mismatch. Four retained proofs/zero definitions/newproofcode/registry nodes: Theorem2.8, following mandatory unnumbered interiorzero consequence, and two explicit library helpers; not4printedtheorems. Source Vnonemptyconvex/xmember, f convex and differentiable over open set containingV. Compare source neighborhood premise with actual ConvexOn V F and explicit finite/differentiable canonical F on arbitrary open U. This is a stronger terminal with an explicit premise delta, not equivalence of assumptions. Audit interpretation of source function/convexity over neighborhood; don't add a convex U hypothesis to actual target. Public canary constructs source ConvexOn U F then restricts to V. Both infinities allowed outside U, no global noBottom/finite/convex F. Canonical F embeds as f on finite U by actual coe_toReal, giving local derivative meaning near feasible x. Do not import previous helper's global noBottom premise silently here.

Real helper is everywhere-real ConvexOn V/x membership/ambient derivativeatx, no openV/EReal representation. Finite minimum-order bridge requires finite values only onV (both infinities excluded), membershipexplicit; no convexity/topology/derivative. Source terminal has allfeasible y, IsMinOn alone lacks membership. Interiorzero iff adds AMBIENT interiorV; boundary minimum neednotzero. No existence/uniqueness/closedness/boundedness/strictconvexity. General complete real Hilbert context explicitly extends Rd. Actual Fermat API has fallbackzero for nondifferentiability, but frozen hd remains; inspect gradient meaning rather than using fallback to claimsource.

Actual current public4bodies/types/APIs/scoped compiled4node graph provided for readiness, not fresh body/canary/axiom/combined acceptance. Exactpoint: realhelper necessity uses actual feasible segment/tangent/derivative, sufficiency accepted supportingbound; finitebridge exactfiniteorder; terminals compose then localFermat. Existing canary nonzero-gradient boundary1 onV=[1,infinity), lossidentityonU=(0,infinity), finite/differentiable/sourceconvexUrestriction, smaller0.5outsideV/larger2inside; nonconstant quadratic on open nonclosed V=(-1,infinity) interior0/gradient0/values0vs1. Fresh replay pending. Old same-actor reviews retained but not accepted as distinct review. Current selectedreader supplied to find required qualifications (generic helpernotes currently misleading); separate body/final reader phases follow.

Write ONLY source-contract-review-v1.md/source-contract-receipt-v1.json here, actor.task=/root/source_reviewer, verdict, target_verdicts/four7slot differences, mathematical_repairs and required_reader_corrections separate, exact reviewed_files/reportpath/SHA. No input edits/human/external/runtime-model attestation. Whole Chapters1-16 Goalactive/Chapter2null/incomplete/18legacybeforepackage; previous OPENdraftPR158c9b47... unmerged; no main/live/chapter/book acceptance.''')
paths={p.as_posix() for p in run.rglob('*') if p.is_file()}
paths.update(p.as_posix() for p in Path('docs/contracts/online-optimality-migration-v1').rglob('*') if p.is_file())
paths.update(p.as_posix() for p in Path('docs/contracts/online-optimality-v1').rglob('*') if p.is_file())
paths.update(['BanditRLProof/OnlineConvexOptimality.lean','Tests/OnlineConvexOptimalityCanary.lean','Tests/OnlineConvexFirstOrderCanary.lean',
 'BanditRLProof/OnlineConvexFirstOrder.lean','BanditRLProof/OnlineConvexExtended.lean',
 '../research-online-ogd/tmp/pdfs/orabona-v10.pdf',graph_path,'.lake/packages/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean',
 '.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean','.lake/packages/mathlib/Mathlib/Analysis/Convex/Deriv.lean',
 '.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean','.agents/skills/bandit-semantic-roundtrip/SKILL.md',
 'website/content/readings.json','website/content/highlights.json','website/content/chapters.json','lean-toolchain','lakefile.lean','lake-manifest.json',
 'tasks/ONLINE-OPTIMALITY-MIGRATION-20261005.md','conversion-windows/ONLINE-OPTIMALITY-MIGRATION-20261005.md','proof-obligations/ONLINE-OPTIMALITY-MIGRATION-20261005.md',
 'runs/online-first-order-migration-20261005/accepted-decision-v1.json','runs/online-first-order-migration-20261005/native-acceptance-overlay-v1.json',
 'runs/online-first-order-migration-20261005/pr-delivery-v1.json'])
write('contract-source-inputs-v1.json',dict(scope='four retained optimality contracts only',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Optimality contract fixed inputs',len(paths),'actual scoped edges',len(graph['edges']),'; source verdict pending.')
