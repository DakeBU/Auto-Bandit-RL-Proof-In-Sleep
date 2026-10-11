from common import *
assert load(RUN/'benchmark-public-probe-v2.json')['actual_exit'] == 0
assert load(RUN/'benchmark-direct-parent-checks-v1.json')['all_expected_found']
assert load(RUN/'algorithm-canary-type-probe-v2.json')['actual_exit'] == 0
capture('resume-canonical-baseline-v4','git','-C','E:/ABRL/research','rev-parse','HEAD','origin/main')
capture('resume-canonical-dirty-v4','git','-C','E:/ABRL/research','status','--porcelain=v1')
capture('resume-own-baseline-v4','git','rev-parse','HEAD','--git-common-dir')
frontier = dict(package=TASK, branch=BRANCH, base=BASE, Goal_status='ACTIVE',
    stage='Source Eq4.4/Theorem4.14 and canonical BODYs reviewed; full benchmark/attainment/source conjunction compiled with full public/fence/axiom/VALUE evidence; benchmark BODY and actual-run canary CONTRACT distinct review pending.',
    own_production=rows([ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean',ROOT/'BanditRLProof/OnlineAdaptiveBenchmark.lean',PUBLIC]),
    source_endpoint_BODY_review_sha256=sha(RUN/'specialization-BODY-benchmark-CONTRACT-review-v1.json'),
    benchmark=dict(five_full_BODYs_present=True, actual_sequential_focus=True, full_public=True,
        standard_axioms=True, frozen_headers=True, selected_direct_VALUE=True, BODY_review='pending',
        source_repair='Separately reviewed infimum/attainment correction; literal min not claimed in mixedzero cases.'),
    canary=dict(seven_full_headers=True, context='draft-v2', TYPE_success=True,
        full_neutral_reconstruction=True, CONTRACT_review='pending', production_BODYs_present=False),
    failures=[dict(kind='Production GLB BODY', actual_exit=1, residual='b²+D²*0=b²',
        repair='Append ring only', corrected_focused_actual_exit=0),
        dict(kind='External public application probe', actual_exit=1,
        reason='Probe omitted new owning module import', repair='Add import in versioned probe only',
        corrected_public_actual_exit=0)],
    current_frontier=['Distinct benchmark BODY verdict','Seven actual-run canary CONTRACT/BODY/public/axiom/fence/VALUE/BODY review',
        'Combined root Tests full harness, same registry/Book/reader, shadow/site/pixels/FINAL/native/post-native/delivery'],
    chapter='Chapter2 partial/null; all eight required forward containers open until exact obligations close.',
    other_chapters='Chapter1 prior accepted-local; Chapters3-16 unenumerated/null; no new chapter gate.',
    delivery='No current package commit/push/PR/merge/deploy; PR217 exact unmerged head is stacked base.')
write(RUN/'causal-frontier-v4.json',frontier)
digest='''Four source-convex/canonical endpoints now have actual proofs and favorable distinct BODY review. Five exact benchmark/attainment/repaired source-conjunction BODYs compile sequentially, preserve all original headers, publicly instantiate complete conclusions, have five standard-only axiom outputs and selected compiled direct VALUE parents. Mixedzero GLB greatestness uses explicit small objective values, not strict improvement alone; exact source conjunction uses one actual realized energy. First GLB local residual required ring only; initial public probe lacked owning-module import. Both real failure outputs/snapshots retained, corrected in separately versioned BODY/probe and actual successes recorded. No statement weakening or source mutation.

Seven complete actual-run canary statements and context TYPE-check; distinct neutral decoder reconstructs every component. Existing shared affine producer APIs were retrieved; proposed context v2 adds their existing module only before CONTRACT review, without header/neutral changes. Benchmark BODY and canary CONTRACT review pending, so no production Test BODY yet. Remaining full package gates and current source scope remain open. This is local digest/ledger, no certified global memory or native acceptance. Whole Goal ACTIVE.
'''
write(RUN/'memory-digest-v4.md',digest)
addition='\n\n## Current causal source terminal frontier v4\n\nLatest snapshot: runs/online-ch2-adaptive-osd-20261010/causal-frontier-v4.json. Earlier pending descriptions are historical. '+digest+'\n'
for folder in ['proof-obligations','conversion-windows','research-wiki/retrieval-index']:
    path=ROOT/folder/(TASK+'.md')
    before=path.read_bytes()
    write(RUN/('before-causal-frontier-v4-'+folder.replace('/','-')+'.md'),before)
    path.write_bytes(before+addition.encode('utf8'))
event('benchmark-candidate-event-v1','candidate',dict(current_leaf='source_theorem4_14_infimum',
    public_sha256=sha(RUN/'benchmark-public-probe-v2.json'),
    frontier_sha256=sha(RUN/'causal-frontier-v4.json'),
    boundary='Local candidate only; distinct BODY review and actual-run canary/full package gates open.'))
print('v4 frontier records actual source/benchmark progress and failures; no acceptance.',flush=True)
