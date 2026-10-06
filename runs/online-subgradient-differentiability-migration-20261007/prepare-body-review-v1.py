"""Bind the actual fixed producer bodies, genuine canaries and kernel/graph gates."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;contract=Path('docs/contracts/online-subgradient-differentiability-migration-v1');task='ONLINE-SUBGRADIENT-DIFFERENTIABILITY-MIGRATION-20261007'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes((x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
labels=['retained-module-v1-01','public-body-v1-01','public-canary-focused-v1-01','public-all-axioms-v1-01','verify-public-fences-v1-01','compiled-public-graph-v1-01','boundary-leaf-v2-01']
for label in labels:assert load(run/(label+'-exit.json'))['exit_code']==0,label
jobs={}
for label in ['retained-module-v1-01','public-canary-focused-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
assert jobs=={'retained-module-v1-01':3315,'public-canary-focused-v1-01':9091}
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineSubgradientDifferentiability.lean')
for group in ['module','whole_old_canary','fixed_shared_files']:
 for p,h in freeze[group].items():assert sha(p)==h,p
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
assert Path('Tests.lean').read_bytes().startswith((run/'original-Tests.lean.txt').read_bytes())
for n,row in load(contract/'new-canary-terminals-v1.json')['headers'].items():assert lean_declaration_header(Path('Tests/OnlineDifferentiabilityBoundaryCanary.lean'),n)==row['statement']
r=load(run/'source-contract-receipt-v1.json');assert sha(r['report'])==r['report_sha256']
snap={(row['path'],row['raw_sha256']):row['snapshot'] for row in load(run/'historical-raw-supersession-v3.json')['rows']};oldrows=[]
for row in r['reviewed_files']:
 p,h=row['path'],row['sha256'];resolved=p if sha(p)==h else snap[(p,h)];assert sha(resolved)==h,p
 oldrows.append(dict(path=p,sha256=h,resolved=resolved))
write('prior-contract-binding-v1.json',dict(status='passed',rows=oldrows,original_receipt_immutable=True))
raw=(run/'public-all-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
names=load(run/'canary-integration-before-public-use-v1.json')['named_axiom_targets']
assert len(matches)==len(names)==20 and {n for n,a in matches}==set(names)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
gp=Path('tmp/online-subgradient-differentiability-migration-public-graph-v1.json');g=load(gp)
assert g['extraction']['source']=='compiled-environment' and len(g['nodes'])==21 and len(g['edges'])==3026
assert sum(n['kind']=='theorem' for n in g['nodes'])==20 and sum(n['kind']=='definition' for n in g['nodes'])==1 and all(n['has_value'] for n in g['nodes'])
assert {n['name'] for n in g['nodes']}==set(names)|{'BanditRL.OnlineConvex.SourceDifferentiableAt'}
oldg=load(run/'compiled-ready-graph-v3.json');newmap={n['name']:n for n in g['nodes']}
assert all(n==newmap[n['name']] for n in oldg['nodes'])
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']};pre='BanditRL.OnlineConvex.'
required=[(pre+a,pre+b) for a,b in load(run/'ready-dependencies-v3.json')['required_value_pairs']]
required.extend([('ForwardSubgradientProbe.constrained_interval_singleton',pre+'theorem_2_22_gradient'),('ForwardSubgradientProbe.quadratic_singleton_nonzero',pre+'theorem_2_22_gradient'),('DifferentiabilityProbe.constrained_interval_differentiable',pre+'theorem_2_22'),('DifferentiabilityProbe.quadratic_derivative_nonzero',pre+'singleton_subdifferential_hasGradientAt'),('DifferentiabilityProbe.interval_boundary_not_differentiable',pre+'theorem_2_22'),('Tests.OnlineDifferentiabilityBoundary.singleton_not_sourceDifferentiable',pre+'sourceDifferentiableAt_regular')])
assert len(required)==20
for a,b in required:assert (a,b) in pairs,(a,b)
write('compiled-public-graph-v1.json',gp.read_text(encoding='utf-8'))
write('compiled-dependencies-v1.json',dict(status='passed',nodes=21,proof_nodes=20,definition_nodes=1,direct_references=3026,graph_sha256=sha(gp),required_value_pairs=required,ready_12nodes_exactly_preserved=True,full_graph_export=False,selected_nine_canary_proofs_exported=True))
write('public-actual-bindings-v1.json',dict(status='compiled-public-exact-targets-and-genuine-canaries',module_sha256=sha(public),new_canary_sha256=sha('Tests/OnlineDifferentiabilityBoundaryCanary.lean'),fixed_headers=freeze['headers'],complete_definition_fixed=True,retained_proofs=11,retained_definitions=1,new_production_proofs=0,new_test_proofs=3,whole_old_canary_proofs=6,total_canary_proofs=9,named_kernel_axes=axes,named_kernel_checks=20,native_guards=11,focused_jobs=jobs,selected_graph_nodes=21,selected_graph_direct_references=3026,public_body_fresh_seconds=load(run/'public-body-v1-01-exit.json')['elapsed_seconds'],canary_bundle_compiled_v2=True,first_failure_retained='boundary-first-leaf-v1-01 unknown API not_mem_empty; v2 simpa on same actual empty membership; fixed headers/definition/producer proofs unchanged, no mathematical contract change. New canary unnecessarySimpa linter suggestion remains nonblocking; no suppression.',source_package_accepted=False,chapter_complete=False,goal_complete=False))
write('30_lower_worker-public-evidence-v1.md','All original11proofs/one full definition fixed and actually re-elaborated; publicbody11.25s, retainedfocused3315jobs/newoldcanaryfocused9091jobs,20namedkernel standard3-or-none/no sorryAx,11nativeguards. Three TEST-only singletondiagnostics actuallyprove toRealzero smooth, genuineambientgerm impossible via regularity/domain-emptyinterior, every realglobalsupport; firstAPItypo failedandpreserved/v2pass14.235s/no terminalchange/newlinter nonblocking. Wholeold6canaryproofs nonzeroquadratic/indicatorinterior/boundarytop respected. Actual21selectednodes3026directrefs/20required producer-canary valuepairs/old12nodesexact; notfullgraph. No newproduction mathematical nodes/oneT2.22sourceanchor. Contractaccepted9readerfixes; distinctBODY and combinedrootTests/fullharness/siteFINAL/PRpending, Goalactive.')
packet='''Distinct BODY source review, requested GPT-6 Astra/medium. Hash ALL public-body-inputs-v1.json rows and resolve immutable prior-contract-binding-v1.json (274rawbindings). Exact source Orabona v10 printed17/PDF29 T2.22 ONLYoneanchor: convex EReal f finiteatx, genuine ambient differentiability IFF global support singleton AND every locally agreeing differentiable REAL representative identifies it as its gradient. Main terminal no supplied proper/interior/closed/Lipschitz/continuous/hbot/differentiability of toReal; derive regularity separately. Full unchanged SourceDifferentiableAt and actual11proofbodies/headers/scopedclasses. Definition @type omitsfiniteD, main11proofsfiniteDrealinner/complete derived/zeroD permitted/ambientnonempty. SharedgenericS ALLambienty includesimproperfunctions outsideproperclass, directionshere derive noBottom so genuinefiniteconversions. Convexreal-height epi. Topoutside actual localgerm permitted, no globalREAL restriction. Helpers supplied noBottom/NeBot/Lipschitz/continuity/singleton are interfaces, not silently added to fullsource theorem. Source introductory arbitrary differentiable-function prose interpreted within convex nexttheorem, not false nonconvex generalization.

Review real body route: reverse normal at original convexdomainboundary/nonzero Riesz d would create distinct g+dglobalsupport, forcesinterior; finiteD localconvexLipschitz→boundallnearby supports; continuity/nontrivialfilter→closedgloballimits; compactball/uniqueclusterpoint→actualselectedsupportconvergence; acceptedambientexistence internalchoice G nearx; twoactual supportinequalities andnorminner giveFrechet littleO, HasGradient(toReal)g, recoverfinitegerm. Forward finitegerm→canonicalfinite-neighborhoodcontact/noBottom/regularity/interior; accepted2.7globalfirstorderproducesgradient support; localmin derivativezero/Rieszinjectivityuniqueness; eventualrepresentative equality gives equalgradients; explicitsetidentity/forward/fulliff. Proofinternalchoice notmeasurable/computable/algorithmoracle. Actualproducerbody dependencies verified compiled, no consumer-onlyterminal.

Freshactual11body re-elaboration andfocused3315jobs. Six WHOLEoldcanaryproofs preserved, exercise indicator[0,2]at1/topoutside, nonzeroquadraticgrad2, fullreverse, HasGradient, boundary0 distinctsupports0/-1/fullforward excludes realgerm. Three NEWfrozen TEST-only diagnosticproofs ACTUALLYcompiled v2/public9091jobs: REALsingleton{1} toReal identicallyzero smoothlydifferentiable; trueambient SourceDifferentiableAt impossible from actualregularity/domainemptyinterior; EVERYrealg global support, not falselysingleton. No support/gradient/interiororacle or identicallytop/emptydomain success. Do not generalize REALsingletonemptyinterior to zeroD. Testscriptfirstv1FAILEDunknownidentifiernot_mem_empty; rawfailure/scratchv1+native repair preserved, v2simpausingACTUALempty membership passes14.235s. Frozen3headersunchanged; no contractweakening/productionmathchange. NewunnecessarySimpa linter is nonblocking, preserved unsuppressed. Twenty UNIQUEactualnamedkernelchecks11producer+6old+3newcanaries use standard3or-none/no sorryAx;11nativeguards SEPARATEfrom compilation; full definition tokens/oldmodule bytes/wholeoldcanary/rootBandit/pins/shareddependencies fixed; Testsoriginalrawprefix+onecanaryimport.

Actual selected21nodes3026directtype/value refs=11producerproofs+1complete definition+9canaryproofs;20requiredproducer/canaryvaluepairs; old12node1880readinesssubgraph EXACT retained. Notfullregistry/canarystatistics-invented. OnlynewTEST proofs, ZEROnewproductionmathnodes/defs,11retainedproducer proofs/onecomplete definition supporting ONEsourceanchor. All10811oldsharedregistryIDsURLs expected preserved0new AFTERsitegates. Existing four teachinglinks are notexhaustive proofDAG. Nine CONTRACTreaderfixes still required independently from mathematical repairs.

CONTRACT accepted, currentBODYonly; combinedrootTests/fullharness/history/taskshadow/reader/siteFINAL/PRstillpending. Allowed laterordinaryleadingcomment preservingalloriginalproducerbytes, selected sameBooksubtree in3JSON/manifest; no proof/header/definitiontoken changes. Canonicalmain6847unchanged/OPENdraftPR168exact4cf116base/no main/live/merge/deploy/retirement/globalSGBedit. Legacy7->6ONLYOnlineSubgradientDifferentiability afterfullacceptancePR; Chapter1migration/nineotherlegacycontracts/Chapter2totalnullincomplete/T2.23andlaterrequired/3-16unenumerated/GoalACTIVEunbudgeted. Three distinctautomatedactors requestedAstra medium/honest restrictedpackethistory/no humanexternal/runtime attestation; runtime gates vsfilepromptconventions separate. Readonly/helper/rendering preparationerrors/immutableversionrepairs preserved.

Write ONLY public-body-review-v1.md/public-body-receipt-v1.json here actor.task=/root/source_reviewer, all11targetseven-slots andcomplete definition, actualroute/canaries/graph/gates/explicitdeltas, ALLreviewed_files rawhash/reportSHA, mathematical_repairs versus required_reader_corrections. Inputs immutable; BODYonlyneverwholepackage/chapterGoal acceptance.
'''
write('public-body-review-packet-v1.md',packet)
paths={row['path'] for row in load(run/'contract-source-inputs-v3.json')['rows']}
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file());paths.update(p.as_posix() for p in contract.rglob('*') if p.is_file());paths.update(['Tests/OnlineDifferentiabilityBoundaryCanary.lean',gp.as_posix()])
write('public-body-inputs-v1.json',dict(scope='11retainedproofs1complete definition/9genuinecanaries/20namedkernelchecks/11guards/21selectednodes3026refs',source_package_accepted=False,chapter_complete=False,goal_complete=False,rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Actual completeproducer bodies/9canaries/20kernel axes/11guards/21nodes3026refs bound; distinct BODYpending.')
