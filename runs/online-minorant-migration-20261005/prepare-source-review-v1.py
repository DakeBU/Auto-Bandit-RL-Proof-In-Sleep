"""Bind exact affine support/minorant scopes and actual compiled dependencies."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
for label in ['retained-module-types-v1-01','actual-public-types-v1-01','actual-pinned-APIs-v1-01','actual-scoped-graph-v1-01']:assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v1.json')
for p,h in dict(freeze['module'],**freeze['canary']).items():assert sha(p)==h,p
blind=load(run/'blind-receipt-v1.json');assert sha(run/'blind-packet-v1.md') in json.dumps(blind) and sha(run/'blind-reconstruction-v1.md') in json.dumps(blind)
gp='tmp/online-minorant-migration-scoped-graph-v1.json';graph=load(gp)
assert graph['root_module']=='BanditRLProof' and graph['extraction']['source']=='compiled-environment'
assert {n['name'].rsplit('.',1)[-1] for n in graph['nodes']}==set(freeze['headers']) and all(n['has_value'] and n['kind']=='theorem' for n in graph['nodes'])
pairs=[]
for e in graph['edges']:
 if e['target'].startswith('BanditRL.OnlineConvex.') and (e['kind']=='value' or e['also_in_value']):pairs.append([e['source'],e['target']])
for a,b in [('affine_support_of_finite_neighborhood','supporting_functional_at_closure'),('affine_support_of_domain_interior','affine_support_of_finite_neighborhood'),('affine_minorant_of_domain_interior','affine_support_of_domain_interior'),('convex_affine_minorant','affine_minorant_of_domain_interior'),('convex_affine_minorant','convex_effectiveDomain')]:assert ['BanditRL.OnlineConvex.'+a,'BanditRL.OnlineConvex.'+b] in pairs
write('ready-dependencies-v1.json',dict(status='actual-compiled-scoped-ready',graph_path=gp,graph_sha256=sha(gp),scope_nodes=len(graph['nodes']),actual_edges=len(graph['edges']),project_proof_pairs=pairs,new_export=True,full_graph_export=False,canary_graph_export=False,existing_retained_bodies=True,package_accepted=False))
(run/'compiled-scoped-graph-v1.json').write_bytes(Path(gp).read_bytes())
write('source-review-packet-v1.md','''Required distinct CONTRACT review GPT6Astra/medium. Independently hash every contract-source-inputs-v1.json row, reread frozen Orabona v10 Theorem2.9 p11/PDF23 parent, actual4headers/commoncontexts/public@types/pinnedAPIs/neutraldecoder/currentactual4nodecompiledgraph and oldcontracts. These4retained LIBRARY results are necessary affine-support/minorant dependencies, not4printedsource results or Jensenacceptance. Sourceparentf measurable/no-bottom/integrableX/probability/AEdom are parent conditions, not all assumptions of this geometric dependency. Globalminorant supplies future negative-part producer; source loss-integrability may not be added.

Check all4actualtypes finite-dimensional realnormedE, NO supplied MeasurableSpaceE/BorelSpaceE/probability/innerproduct/CompleteSpace classes. Oldv1prose retainedBorel is stale/historical, not an instruction to silently add or erase actualtype parameters. SourceEuclidean included by explicitlyreviewednormedfiniteD generality; no arbitraryinfiniteD extension. Convexextended predicate is actual convex REAL-height epigraph; effectiveDomain=f<top generallyincludesbottom, globalhbot suppliesgenuinefinite ondomain. Sourceglobalno-bottom retained where supplied, firsthelper must actuallyproduceit.

N01 genuineeventually-neighbourhood finiteness notfiniteatxalone, epigraphconvex ->globalrealcontinuousaffine support TOUCHINGf(x), outputa mayzero; no suppliedhbot/closedness/lsc/fmeas/diff. Body generatesepigraphboundary usingauxverticalidentity localmin contradiction; actualnonzero separatorL onE x R splitA/c; upwardepi c<=0; localfinite/auxlinear localmax→c!=0→c<0; legaldivision andsupport actuallyderiveglobalnoBottom andaffinesupport. Noassumedverticalnegativecoefficient/desiredsupport oracle. Differentiabilityonlyauxid/A, notlossf.

N02 globalhbot/convexepi/xAMBIENTdomaininterior ->globalTOUCHINGsupport; firsthelper'sfinite-neighbourhood mustbeproduced. N03 samepremises ->globalminorant dropscontact; no interiordischarge/nonzero slope/uniqueness. N04 globalhbot/convexepi/NONEMPTYdomain only ->∃continuousreal a,b,ALLx a(x)+b<=f(x), includingtopoutside. Noambientinterior/closedness/lsc/fmeas/finite-support/boundedness/fdiff/chosencontactatboundary/quantitative bound/positive dimension premise. Actual producer generatesdomainconvexity/intrinsicinterior inaffinespan, translatesdirectionpullback, provesambientinterior there, appliesinteriorhelper, actuallyextendslinearfunctional/continuity/interceptcorrection globally. No assumed desiredminorant orambientinterior substituted; no zero-functional prohibition.

Meaningful oldpubliccanary scalarcoordinate onNONCLOSED lowerdim ray withtopoutside, actuallossformula/noBot/convex/domain=ray/generalminorant/values1/3/top+¬closed. UpperAdd used with everywherefinite basecoordinate, no mixed-infinity source-convention claim. Sixproofs/onecanarydef bytesfixed;11namedaxioms planned (4public+6canaryproof+1def). No probability/Jensenloss conclusion. Readiness currentmodule/types/APIs/scopedgraph ONLY, notcandidatefreshfullcanary/axiom/root/Tests/harness/site. Readercurrentlyonly2representativelinks/highlights butmodule/sharedregistry includes4; preserveoldURLs, clarifyactualproofbody/parent/class/finite-neighbourhood/interior/contact/globalbound distinctions. Identifyrequiredreadercorrections vs mathematicalrepairs, no targetweakening. Defaultsinglelowerreadyfinite-neighbourhoodleaf; distinctbody/final/package/PRgates follow.

Stacked OPENdraftPR161f68646457a12de93ee6cb8d585a4162f9f0a112c, notmain; legacy15beforepackage/Chapter2mandatorynull/incomplete/wholeChapters1-16realGoalACTIVEunbudgeted. Prioracceptedreceipts/reports/snapshots/failures immutable. Write ONLYsource-contract-review-v1.md/source-contract-receipt-v1.json here, actor.task=/root/source_reviewer, verdict/4actualtarget_verdicts/sevenslots, mathematical_repairs separatelyrequired_reader_corrections, allreviewed_files rawSHA/reportpathSHA. Do not editinputs orclaimhuman/external/runtimeattestation.''')
paths={p.as_posix() for p in run.rglob('*') if p.is_file()}
for folder in ['docs/contracts/online-minorant-migration-v1','docs/contracts/online-minorant-v1','docs/contracts/online-minorant-interior-v1']:
 base=Path(folder)
 if base.exists():paths.update(p.as_posix() for p in base.rglob('*') if p.is_file())
paths.update(['BanditRLProof/OnlineConvexMinorant.lean','Tests/OnlineConvexMinorantCanary.lean','BanditRLProof/OnlineConvexBarycenter.lean','Tests/OnlineConvexBarycenterCanary.lean','BanditRLProof/OnlineConvexExtended.lean','BanditRLProof/OnlineConvexSums.lean','BanditRLProof/OnlineJensen.lean','../research-online-ogd/tmp/pdfs/orabona-v10.pdf',gp,'.agents/skills/bandit-semantic-roundtrip/SKILL.md',
'.lake/packages/mathlib/Mathlib/Analysis/Convex/Intrinsic.lean','.lake/packages/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean','.lake/packages/mathlib/Mathlib/Analysis/Normed/Affine/Isometry.lean','.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean','.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean',
'website/content/readings.json','website/content/highlights.json','website/content/chapters.json','lean-toolchain','lakefile.lean','lake-manifest.json','tasks/ONLINE-MINORANT-MIGRATION-20261005.md','conversion-windows/ONLINE-MINORANT-MIGRATION-20261005.md','proof-obligations/ONLINE-MINORANT-MIGRATION-20261005.md','runs/online-barycenter-migration-20261005/accepted-decision-v1.json','runs/online-barycenter-migration-20261005/native-acceptance-overlay-v1.json','runs/online-barycenter-migration-20261005/pr-delivery-v1.json'])
write('contract-source-inputs-v1.json',dict(scope='four retained affine-support/minorant contracts only, no Jensenacceptance',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Minorant contract fixedinputs',len(paths),'actualnodes',len(graph['nodes']),'edges',len(graph['edges']),'; distinctsource verdictpending.')
