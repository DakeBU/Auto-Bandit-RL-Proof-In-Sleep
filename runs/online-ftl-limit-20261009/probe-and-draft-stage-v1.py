from common_v1 import *
fixed()
gate('api-probe-v1','lake','env','lean',RUN/'api-probe-v1.lean')
gate('draft-mathlib-cards-v1','rg','-n','MLIB-ASYMPTOTICS|MLIB-REAL-LOG-SQRT',ROOT/'research-wiki/mathlib/theorem-cards.md')
write(CONTRACT/'reuse-decision-v1.json',dict(
    decision='adapt_existing',new_production_file=PUBLIC.relative_to(ROOT).as_posix(),
    local_reused=['empiricalMean_minimizes','empiricalMean_decomposition','squaredLoss_minimum_eq',
        'squaredBestRegret_eq_comparatorRegret','meanPredict_bestRegret_bound','LimitNoRegret'],
    actual_decl_search_logs=['draft-search-mean-v1.log','draft-search-regret-v1.log','draft-search-limit-v1.log'],
    absence_query='draft-local-absence-v1.log exit1 means no exactnewnamehits; notproofsuccess',
    mathlib_API_log='api-probe-v1.log',mathlib_cards='draft-mathlib-cards-v1.log',
    new_general_mathlib_lemma=False,new_external_dependency=False,external_library_scope='No Optlib/LML fact or dependency used; pinned compatible mathlib owns algebra/limits.',
    real_consumers={'F1':['F3 best-regret squeeze','same-FTL source signedregret audit'],
        'F2':['F4 exactordinarylimit criterion','finitefixedcomparator reader formula']},
    imports=['BanditRLProof.OnlineSquareMinimum','BanditRLProof.OnlineNoRegretSemantics'],
    no_duplicate_wrapper=True,proof_route='Recorded single prefixminimum induction, exactdecomposition, actual4logupper squeeze and limit arithmetic.'))
native('draft-help-lifecycle-v1','lifecycle-event','--help')
native('draft-lifecycle-v1','lifecycle-event','--session',TASK,'--event','draft','--payload-json',
    json.dumps(dict(run_id=RUN.name,contract_version=1,source_sha256=PDF_SHA,
        target_statement_hashes=[t['statement_hash'] for t in load(CONTRACT/'targets-v1.json')['targets']],
        obligations=5,compiled=0,chapter_complete=False,goal_complete=False)))
print('Actual draft event and pinned API retrieval retained; no new proof body.',flush=True)
