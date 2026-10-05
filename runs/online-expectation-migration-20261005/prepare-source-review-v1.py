"""Freeze actual signed-integral definitions, types and proof-value readiness."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as h:
  if isinstance(x,str):h.write(x.rstrip('\n')+'\n')
  else:json.dump(x,h,ensure_ascii=False,indent=2);h.write('\n')
for label in ['retained-module-types-v1-01','actual-public-types-v1-01','actual-scoped-graph-v1-01','actual-pinned-API-retrieval-v1-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v1.json')
for p,h in dict(freeze['module'],**freeze['canary']).items():assert sha(p)==h,p
blind=load(run/'blind-receipt-v1.json')
assert sha(run/'blind-packet-v1.md') in json.dumps(blind) and sha(run/'blind-reconstruction-v1.md') in json.dumps(blind)
gp='tmp/online-expectation-migration-scoped-graph-v1.json';graph=load(gp)
assert graph['root_module']=='BanditRLProof' and graph['extraction']['source']=='compiled-environment'
assert {n['name'].rsplit('.',1)[-1] for n in graph['nodes']}==set(freeze['headers']) and all(n['has_value'] for n in graph['nodes'])
assert sum(n['kind']=='definition' for n in graph['nodes'])==3 and sum(n['kind']=='theorem' for n in graph['nodes'])==7
pairs=[]
for e in graph['edges']:
 if e['target'].startswith('BanditRL.OnlineConvex.') and (e['kind']=='value' or e['also_in_value']):pairs.append([e['source'],e['target']])
for a,b in [('negativeIntegral_coe_ne_top','positiveIntegral_coe_ne_top'),('signedExpectation_coe_integrable','positiveIntegral_coe_ne_top'),('signedExpectation_coe_integrable','negativeIntegral_coe_ne_top'),('signedExpectation_eq_top','signedExpectation')]:
 assert ['BanditRL.OnlineConvex.'+a,'BanditRL.OnlineConvex.'+b] in pairs,(a,b)
write('ready-dependencies-v1.json',dict(status='actual-compiled-scoped-ready',graph_path=gp,graph_sha256=sha(gp),scope_nodes=len(graph['nodes']),actual_edges=len(graph['edges']),project_proof_pairs=pairs,new_export=True,full_graph_export=False,canary_graph_export=False,existing_retained_bodies=True,package_accepted=False))
(run/'compiled-scoped-graph-v1.json').write_bytes(Path(gp).read_bytes())
write('source-review-packet-v1.md','''Required distinct CONTRACT review GPT-6 Astra / medium. Rehash every contract-source-inputs-v1.json row. Review fresh Orabona v10 Theorem2.9 p11PDF23, seven retained helpers/three actual definition bodies/frozen headers/scoped context, neutral decoder, actual pinned APIs and current compiled graph. Source Theorem2.9 is the parent, not seven printed foundation statements; this is a necessary representation dependency only. Arbitrary measure and Omega, no probability/mass/normalization/sigma-finite/function-measurability premise for definitions and coercion identities. Distinguish total lintegral/arithmetic from mathematical signed-integral interpretation. Both-infinite totalized top-top is bottom in pinned EReal; it is not a legitimate signed expectation. At least one finite part and measurable interpretation needed. No claim that definition is conditionally typed or enforces this semantic condition at runtime.

Actual Integrable real-f prerequisites for two finite-parts proofs and embedded Bochner compatibility retain a.e. strong measurability and finite norm integral. No arbitrary nonintegrable Bochner-zero substitution. A.e. nonnegative extended f needs neither supplied measurability nor integrability for actual algebraic reduction; positive infinity retained, negative part provedzero. Infinite-positive result has explicit negative!=infinity. Parent Jensen under measurable convex/noBottom/integrableX/probability/a.e.domain assumptions must prove negative-part finite via global affine minorant, not assume loss integrability. That future dependency/body acceptance is not obtained here.

Public actual existing canary: dirac(-1)+dirac3 has MASS TWO, identity integral2, not probability expectation1; growing n=n+1 with counting measure has finite nonconstant values, positive integral infinity, negative0, signed top. Counting law not probability; not the parent's positive-infinite probability canary. Six canary proofs/two definitions, three production definitions/seven proofs, all bytes unchanged for current readiness; fresh qualified-module/canary/18namedaxioms/10guards/root/Tests/fullharness/reader/site remain pending. Fresh10node direct type/value scoped graph, not full/canary export. Review proof readiness but separate BODY phase will bind fresh actual public replay. Existing reader should clearly distinguish source parent from helpers/arbitrary measure/canary boundary and stale still-unproved wording from historical retained Jensen proof needing distinct revalidation. Do not accept parent/Chapter2/book from foundation proof.

Write ONLY source-contract-review-v1.md and source-contract-receipt-v1.json in this run, actor.task=/root/source_reviewer, verdict accepted|rejected|accepted-with-explicit-delta, target_verdicts for all10 actualnames, seven slots, mathematical_repairs vs required_reader_corrections separate, reviewed_files with exact paths/SHA plus report path/SHA. Do not edit inputs or manufacture human/external/runtime model attestation. Whole Chapters1-16 Goalactive/Chapter2null/incomplete/legacy17beforepackage; OPENdraftPR1597c3b241... unmerged; no main/live/book acceptance.''')
paths={p.as_posix() for p in run.rglob('*') if p.is_file()}
for folder in ['docs/contracts/online-expectation-migration-v1','docs/contracts/online-expectation-v1']:
 paths.update(p.as_posix() for p in Path(folder).rglob('*') if p.is_file())
paths.update(['BanditRLProof/OnlineExpectation.lean','Tests/OnlineExpectationCanary.lean','BanditRLProof/OnlineJensen.lean',
 '../research-online-ogd/tmp/pdfs/orabona-v10.pdf',gp,'.agents/skills/bandit-semantic-roundtrip/SKILL.md',
 '.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean',
 '.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean',
 '.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean','.lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean',
 'website/content/readings.json','website/content/highlights.json','website/content/chapters.json',
 'lean-toolchain','lakefile.lean','lake-manifest.json',
 'tasks/ONLINE-EXPECTATION-MIGRATION-20261005.md','conversion-windows/ONLINE-EXPECTATION-MIGRATION-20261005.md','proof-obligations/ONLINE-EXPECTATION-MIGRATION-20261005.md',
 'runs/online-optimality-migration-20261005/accepted-decision-v1.json',
 'runs/online-optimality-migration-20261005/native-acceptance-overlay-v1.json','runs/online-optimality-migration-20261005/pr-delivery-v1.json'])
write('contract-source-inputs-v1.json',dict(scope='signed expectation representation dependency only, no Jensen acceptance',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Contract fixed inputs',len(paths),'actual scoped nodes',len(graph['nodes']),'edges',len(graph['edges']),'; distinct source verdict pending.')
