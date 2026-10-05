"""Bind exact nonclosed barycenter scopes and actual compiled proof dependencies."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as handle:
  if isinstance(x,str):handle.write(x.rstrip('\n')+'\n')
  else:json.dump(x,handle,ensure_ascii=False,indent=2);handle.write('\n')
for label in ['retained-module-types-v1-01','actual-public-types-v1-01','actual-scoped-graph-v1-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v1.json')
for p,h in dict(freeze['module'],**freeze['canary']).items():assert sha(p)==h,p
blind=load(run/'blind-receipt-v1.json')
assert sha(run/'blind-packet-v1.md') in json.dumps(blind) and sha(run/'blind-reconstruction-v1.md') in json.dumps(blind)
gp='tmp/online-barycenter-migration-scoped-graph-v1.json';graph=load(gp)
assert graph['root_module']=='BanditRLProof' and graph['extraction']['source']=='compiled-environment'
assert {n['name'].rsplit('.',1)[-1] for n in graph['nodes']}==set(freeze['headers']) and all(n['has_value'] and n['kind']=='theorem' for n in graph['nodes'])
pairs=[]
for edge in graph['edges']:
 if edge['target'].startswith('BanditRL.OnlineConvex.') and (edge['kind']=='value' or edge['also_in_value']):pairs.append([edge['source'],edge['target']])
for helper in ['supporting_functional_at_closure','supporting_functional_ae_eq_mean']:
 assert ['BanditRL.OnlineConvex.integral_mem_convex_finiteDimensional','BanditRL.OnlineConvex.'+helper] in pairs
write('ready-dependencies-v1.json',dict(status='actual-compiled-scoped-ready',graph_path=gp,graph_sha256=sha(gp),scope_nodes=len(graph['nodes']),actual_edges=len(graph['edges']),project_proof_pairs=pairs,new_export=True,full_graph_export=False,canary_graph_export=False,existing_retained_bodies=True,package_accepted=False))
(run/'compiled-scoped-graph-v1.json').write_bytes(Path(gp).read_bytes())
write('source-review-packet-v1.md','''Required distinct CONTRACT review GPT-6 Astra / medium. Independently hash every contract-source-inputs-v1.json row, sourcev10Theorem2.9 printed11/PDF23, actual3frozenheaders/separate scopedcontexts/actual @types/neutraldecoder/pinned APIs and scopedcompiled graph. SourceJensen is parent, these3libraryresults necessary nonclosed-convex barycenter dependencies, not3printedsource statements or Jensen acceptance. Actual terminal mean in s ITSELF, no closedness/nonempty fullinterior/finite-support/boundedness/MeasurableSet s assumption. Finite-dimensional real normed generality includes sourceEuclidean; no infinitedimension extension of arbitrarynonclosed membership claimed.

Audit actual scopes separately: equalityhelper Complete realnormedE/noFiniteDim or supplied measurableE, probabilitymu/IntegrableX/continuouslinear a/AE a(X)<=a(meanX) ->AE equality of FUNCTIONAL VALUES, notXconstant/nonzero existence. Geometrichelper finiteDimE/Convexs/xclosure/notAMBIENTinteriors ->nonzeroCLfunctional a withall feasiblea(y)<=a(x); no probability/derivative/closedness/fullinterior/strictseparation/relativeinterior/a(x)=0 claim. Actual barycenter has finiteDimE AND RETAINED MeasurableSpaceE/BorelSpaceE in @type, probability, genuine IntegrableX/AE Xins, no separately supplied MeasurableX or measurableSet s. Don't eraseBorelcontext based only header/innerinduction appearance. Dimension0/emptycases governed actualhypotheses; no positive dimension premise.

Inspect DAG readiness/proofterms to avoid assumed desiredendpoint: mathlibclosedConvex integral onlygivesclosure; outside s ->notinterior; separator throughnonemptyinteriorHB or properaffinespan annihilator; supportingAE inequality then linearintegral/probabilityconstant ->AEequality; actualcenter/lift into properkernel, embedding/isometry AE integrability and mean0; affinepreimageconvex/AE membership; strictfinrank descent/stronginduction. No consumerassumption integrabilityoflift/mean0/closedness/terminalmembership replacing producedchain. Source f measurable/noBottom/integrableX/AEdom/probability neededbyparent later; no lossintegrability assumption imported here or Jensen acceptance.

Existing canary actual halfdirac1+halfdirac3 probability law, vector=(x,0), ray={p.1>0,p.2=0} lowerdimension/nonclosed, proven convex/integrable/AE membership/mean(2,0)/nonconstant/¬closed. Threecanarydefs/sevenproofs/one namedprobabilityinstance, wholebytesfixed;14uniqueaxiomnames planned. Threeunchangedproduction proofs/no defs/new code/nodes. Readiness initialmodule/types/actual scoped3nodegraph not candidatefullcanary/axiom/root/Tests/harness acceptance. Existingreader may conflateallhelperregularity andstaleunprovedparent wording; identify precise requiredcorrections versus mathrepairs, finalbody/readerphases separate. Preserved preceding OPENdraftPR160b2b70... actualbase, notmain; wholeGoalACTIVE/Chapter2null/incomplete/legacy16beforepackage.

WriteONLY source-contract-review-v1.md/source-contract-receipt-v1.json here, actor.task=/root/source_reviewer, verdict accepted|rejected|accepted-with-explicit-delta, target_verdicts3actualnames/sevenslots, mathematical_repairs versus required_reader_corrections, exactreviewedfiles/reportpath/SHA. Do not editinputs orclaim human/external/runtimeattestation. Separatebody/combined/final/package/PRgates remain required.''')
paths={p.as_posix() for p in run.rglob('*') if p.is_file()}
for folder in ['docs/contracts/online-barycenter-migration-v1','docs/contracts/online-barycenter-v1','docs/contracts/online-barycenter-support-v1','docs/contracts/online-barycenter-separation-v1']:
 base=Path(folder)
 if base.exists():paths.update(p.as_posix() for p in base.rglob('*') if p.is_file())
paths.update(['BanditRLProof/OnlineConvexBarycenter.lean','Tests/OnlineConvexBarycenterCanary.lean','BanditRLProof/OnlineConvexMinorant.lean','BanditRLProof/OnlineJensen.lean',
 '../research-online-ogd/tmp/pdfs/orabona-v10.pdf',gp,'.agents/skills/bandit-semantic-roundtrip/SKILL.md',
 '.lake/packages/mathlib/Mathlib/Analysis/Convex/Integral.lean','.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/Separation.lean',
 '.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean','.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean',
 '.lake/packages/mathlib/Mathlib/Analysis/Normed/Affine/AddTorsorBases.lean','.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean',
 '.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean',
 'website/content/readings.json','website/content/highlights.json','website/content/chapters.json','lean-toolchain','lakefile.lean','lake-manifest.json',
 'tasks/ONLINE-BARYCENTER-MIGRATION-20261005.md','conversion-windows/ONLINE-BARYCENTER-MIGRATION-20261005.md','proof-obligations/ONLINE-BARYCENTER-MIGRATION-20261005.md',
 'runs/online-expectation-migration-20261005/accepted-decision-v1.json','runs/online-expectation-migration-20261005/native-acceptance-overlay-v1.json','runs/online-expectation-migration-20261005/pr-delivery-v1.json'])
write('contract-source-inputs-v1.json',dict(scope='three retained nonclosed barycenter/support contracts only, no Jensen acceptance',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Barycenter contract fixedinputs',len(paths),'actualnodes',len(graph['nodes']),'edges',len(graph['edges']),'; distinct source verdict pending.')
