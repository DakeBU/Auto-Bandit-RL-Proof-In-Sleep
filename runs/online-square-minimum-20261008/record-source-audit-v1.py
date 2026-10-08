from common_v1 import *
fixed()
source_rows=[]
for page in [14,15,16,17]:
    for extension in ['txt','png']:
        p=RUN/f'source-pdf{page}-v1.{extension}'
        source_rows.append(dict(path=p.as_posix(),sha256=sha(p),pdf_page=page,printed_page=page-12,
            cache_copy=True,fresh_rerender_claimed=False,root_png_individually_viewed=extension=='png'))
write(RUN/'source-pixel-review-v1.json',dict(status='actual root cached pinned source pixels reviewed',PDF_sha256=sha(PDF),
    pages=source_rows,intent='Source p2 actual square hindsight min; p3 empirical mean argmin; p4 first1/2 and4+4lnT; p5 quarterplus4positive-roundharmonictail.',
    no_reader_or_site_gate_claim=True,source_review_pending=True))
write(CONTRACT/'source-fingerprint-v1.json',dict(PDF=PDF.as_posix(),PDF_sha256=sha(PDF),edition='1912.13213v10,2026-06-21',
    source_pages=source_rows,raw_targets_sha256=sha(CONTRACT/'targets-v1.json'),raw_public_context_sha256=sha(CONTRACT/'public-context-v1.lean'),
    no_source_version_replacement=True,source_review_pending=True))
write(RUN/'retrieval-actual-APIs-v1.json',dict(status='actual local API declarations and exact type compilation',
    card_ids=['MLIB-FINSET-SUMS','MLIB-ORDER-ALGEBRA','MLIB-REAL-LOG-SQRT'],
    general_minimum_adapter='IsLeast.csInf_eq already exists; no duplicate generic theorem planned',
    existing_shared_parents=['empiricalMean_mem','empiricalMean_minimizes','theorem_1_3','meanPredict_regret_refined','comparatorRegret','lemma_1_2'],
    actual_API_gate='actual-draft-types-and-API-v1-exit.json',type_gate='actual-draft-neutral-identities-v1-exit.json',
    actual_memory_queries=['empiricalMean_minimizes','squaredBestRegret','csInf'],
    declaration_presence_is_not_source_acceptance=True,closed_Prop_compilation_is_not_body_proof=True))
oldpath=Path('docs/contracts/online-regret-domains-v1/chapter-one-source-ledger-draft-v1.json')
ledger=load(oldpath)
assert len(ledger['maintext_items'])==16 and ledger['chapter_mandatory_proof_total'] is None
for row in ledger['maintext_items']:
    if row['source_id']=='C1-LOG-UNAVOIDABLE':
        row['current_status']='Bounded qualitative hinge accepted and delivered OPEN/unmerged PR191; actual causal binary-law/seed-expected H/log lower producer, derived coefficient1/6; no chapter closure.'
        row['current_delivery_evidence']='runs/online-log-lower-20261008/delivery-obligations-overlay-v1.json'
    elif row['source_id']=='C1-NOREGRET':
        row['current_status']='Bounded semantic hinge accepted and delivered OPEN/unmerged PR192: ordinary lim distinct from upper, iff under actual finite convergence, one signed-unbounded affine same-process strict obstruction at u=1; no chapter closure.'
        row['current_delivery_evidence']='runs/online-no-regret-20261008/delivery-obligations-overlay-v1.json'
    elif row['source_id']=='C1-REGRET':
        row['square_minimum_subobligation']='REQUIRED current six-target draft actual square interval min/shared comparator/actual FTL adapter; no acceptance yet.'
ledger['version']='square-minimum-draft-v1';ledger['prior_ledger']=dict(path=oldpath.as_posix(),sha256=sha(oldpath),unchanged=True)
ledger['current_package_only']='Actual deterministic square interval hindsight minimum and same signed regret; no IID expected-minimum or expectation exchange.'
ledger['remaining_IID_expected_fixed_minimum_and_causal_cumulative_variance']='REQUIRED next printed1-2/PDF13-14'
ledger['remaining_main_relative_modules']=['OnlineLearningFoundations','OnlineLearningHistory','OnlineLearningIID','OnlineLearningInformation','OnlineLearningStochastic']
ledger['chapter_complete']=False;ledger['goal_complete']=False;ledger['source_package_accepted']=False
ledger['current_planned_new_proofs']=6;ledger['current_planned_new_definitions']=1
write(CONTRACT/'chapter-one-source-ledger-draft-v1.json',ledger)
write(RUN/'proof-obligations-draft-v1.json',dict(contract_version=1,terminals=load(CONTRACT/'targets-v1.json')['rows'],
    obligation_count_scope='Only six fixed new terminal statements',initial_obligations=6,current_unproved=6,
    first_import_ready_leaf='M001',source_stabilization_pending=True,finite_producer_required=True,
    no_assumed_single_step_regret_or_minimizer_certificate=True,remaining_book_obligations=ledger['remaining_IID_expected_fixed_minimum_and_causal_cumulative_variance'],
    chapter_complete=False,goal_complete=False))
fixed();print('Exact pinned four source pages recorded; actual API route and16-item cumulative ledger retained with unknown total.')
