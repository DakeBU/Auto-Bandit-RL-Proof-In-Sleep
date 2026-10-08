from common_reviewed_v2 import *

receipt=reviewed_fixed()
targets=load(CONTRACT/'targets-v2.json')['rows']
for p in APPEND_METADATA + [Path('BanditRLProof.lean'),Path('Tests.lean'),
        Path('research-wiki/retrieval-index/local_lean_declarations.json')]:
    write(RUN/'snapshots'/('CONTRACT-reviewed--'+p.as_posix().replace('/','--')+'.raw'),p.read_bytes())
write(RUN/'stabilized-contract-v2.json',dict(state='stabilized',version=2,
    source_sha256=PDF_SHA, targets_sha256=sha(CONTRACT/'targets-v2.json'),
    context_sha256=sha(CONTRACT/'public-context-v2.lean'),
    source_statement_fingerprint_sha256=sha(CONTRACT/'source-statement-fingerprint-v2.json'),
    source_review_receipt_sha256=REVIEW_RECEIPT_SHA, original_reader_requirements=receipt['reader_requirements'],
    terminal_headers=targets, first_ready_leaf='R001', theorem_bodies_compiled=False,
    package_accepted=False,chapter_complete=False,goal_complete=False))
dag=load(CONTRACT/'initial-DAG-v2.json')
for node in dag['nodes']:
    if node['id']=='R002':
        node['dependencies']=['independent_private_seed_pair','ProbabilityTheory.iIndepFun.indepFun_finset','ProbabilityTheory.IndepFun.comp']
dag['imported_API_route_delta']=receipt['imported_API_DAG_delta']
dag['terminal_headers_unchanged']=True
write(RUN/'reviewed-DAG-v2.json',dag)
for p in APPEND_METADATA:
    p.write_bytes(p.read_bytes()+('\n\n## Stabilized v2; first dependency-ready proving leaf R001\n\n'
        'Actual distinct CONTRACT accepted-with-explicit-delta, exact seven headers/one context frozen. '
        'R002 typed tuple route uses iIndepFun.indepFun_finset and comp, old scalar API is an indirect search lead. '
        'R1–R7 remain future body/canary/reader/gate requirements. R001 joint-law regrouping first; '
        'no package/chapter/Goal accepted at stabilization.\n').encode('utf8'))
native('stabilized-event-v2','lifecycle-event','--session',TASK,'--event','stabilized','--payload-json',
    json.dumps(dict(contract_version=2,frozen_contract=(RUN/'stabilized-contract-v2.json').as_posix(),
        reviewer_receipt_sha256=REVIEW_RECEIPT_SHA, route_DAG_delta_explicit=True)))
native('proving-event-v2','lifecycle-event','--session',TASK,'--event','proving','--payload-json',
    json.dumps(dict(leaf=targets[0]['name'], edit_scope=PUBLIC.as_posix(),
        frozen_terminal_sha256=targets[0]['header_sha256'], single_lower_route=True)))
native('trial-log-help-v2','trial-log','--help')
native('first-worker-running-v2','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','running',
    '--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','PRIVATE-R001-V2','--harness','hierarchical',
    '--target-fingerprint',sha(CONTRACT/'targets-v2.json'),'--notes',
    'First frozen joint-seed regrouping body; natural seed independent whole pair plus X/Y independence, actual product law and measurable associativity. No pairwise shortcut or theorem-type edit.')
context=(CONTRACT/'public-context-v2.lean').read_text(encoding='utf8')
context=context[:context.index('end BanditRL.OnlineLearning')]
body=''' := by
  have hSX : IndepFun S X μ := by
    simpa only [Function.comp_def] using hseed.comp measurable_id measurable_fst
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hS.prodMk hX).aemeasurable hY.aemeasurable).2
  rw [(indepFun_iff_map_prod_eq_prod_map_map hS.aemeasurable hX.aemeasurable).1 hSX]
  apply MeasurableEquiv.prodAssoc.map_measurableEquiv_injective
  rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable ((hS.prodMk hX).prodMk hY)]
  change μ.map (fun ω => (S ω, (X ω, Y ω))) =
    Measure.map MeasurableEquiv.prodAssoc (((μ.map S).prod (μ.map X)).prod (μ.map Y))
  rw [(indepFun_iff_map_prod_eq_prod_map_map hS.aemeasurable
    (hX.prodMk hY).aemeasurable).1 hseed,
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY,
    Measure.prodAssoc_prod]

'''
write(PUBLIC,context+'/-- Joint seed independence and X/Y independence produce the regrouped independent blocks. -/\n'+
    targets[0]['header']+body+'end BanditRL.OnlineLearning\n')
write(RUN/'leaves'/'R001-body-v2.lean',PUBLIC.read_bytes())
headers_fixed(1)
gate('R001-focused-build-v2','lake','build','BanditRLProof.OnlineGuessingRandomizedIID')
native('R001-fence-v2','statement-fence','--declaration',targets[0]['name'],'--file',PUBLIC,
    '--output',RUN/'R001-fence-v2.json')
native('R001-safe-verify-v2','safe-verify','--fence',RUN/'R001-fence-v2.json','--lean-file',PUBLIC)
write(RUN/'R001-kernel-v2.lean','import BanditRLProof.OnlineGuessingRandomizedIID\n#check '+
    targets[0]['name']+'\n#print axioms '+targets[0]['name'])
gate('R001-kernel-v2','lake','env','lean',RUN/'R001-kernel-v2.lean')
native('R001-worker-compiled-v2','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled',
    '--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','PRIVATE-R001-V2','--harness','hierarchical',
    '--target-fingerprint',sha(CONTRACT/'targets-v2.json'),'--new-declaration',targets[0]['name'],
    '--verifier-evidence',RUN/'R001-focused-build-v2-exit.json','--progress-class','compiled-leaf',
    '--obligations-before','7','--obligations-after','6','--notes',
    'Actual frozen R001 body builds and kernel audit, joint seed regrouping only. Six terminals and causal nondegenerate canaries/BODY/root/fullharness/site/FINAL/PR remain.')
write(RUN/'30_worker-R001-v2.md','Actual R001 exact body focused build and kernel audit pass: seed/(X,Y) block-law factorization plus X/Y product law, measurable associative regrouping and injectivity, produced (S,X)/Y independence. This moves causal dependency frontier7→6 only. No supplied target/pairwise assumption shortcut. Remaining source producer terminals and all package/chapter/Goal gates unaccepted.')
write(RUN/'leaf-progress-R001-v2.json',dict(contract_version=2,total_terminals=7,closed=[targets[0]['name']],
    remaining=[r['name'] for r in targets[1:]],public_sha256=sha(PUBLIC),package_accepted=False,
    chapter_complete=False,goal_complete=False))
headers_fixed(1)
print('Actual first frozen R001 body compiled and kernel checked; six mathematical terminals remain.')
