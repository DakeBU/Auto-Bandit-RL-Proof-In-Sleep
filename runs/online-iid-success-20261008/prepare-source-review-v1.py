from common_v1 import *
fixed()
for label in ['typed-api-search-v2','draft-public-target-types-v1','draft-neutral-target-types-v1']:
    assert load(RUN/(label+'-exit.json'))['exit_code']==0
write(CONTRACT/'source-card-v1.json',dict(id=TASK,source=load(CONTRACT/'source-fingerprint-v1.json'),
    source_scope='printed1–2 success Eq1.1/1.2; derived application of Theorem1.3 printed4',
    exact_lean_targets=load(CONTRACT/'targets-v1.json')['targets'],
    original_math='Expected cumulative square loss minus variance*T nonnegative in causal IID model; success means o(T), equivalently average excess tends0. Theorem1.3 actual x1=1/2,xt=mean strictly earlier targets gives signed pathwise min-regret≤4+4lnT.',
    original_index='t1..T becomes t0..T-1; source x1 is Lean meanPredict0; single infinite stream and learner',
    delta_ledger=[
        dict(kind='generalization',target='S001',delta='arbitrary signed total/c, no convergence assumptions, eventual positive horizon arithmetic'),
        dict(kind='source-implicit',target='S002-S004',delta='probability, ambientmeasurability/samelaw and a.s.unit support deriveL2; actual one infinite process'),
        dict(kind='unresolved',target='S002',delta='bounded explicit private-seed jointmeasurable history-policy model; no everykernel/completed-field/AEfactorization representation proved'),
        dict(kind='generalization',target='S003',delta='dependent same-law stream allowed, actual4log upper derivedbyintegrating source pathwise result; not a source-numbered result'),
        dict(kind='same',target='S004',delta='actual strictpastmeanPredict unknown-law learner; IIDnonneg and4logupper produceordinarysuccess; no merelysuppliedconvergence')],
    library_reuse='adapt_existing, no copied probability/asymptotic foundations; no compatible LML import required',
    generic_shared_consumers=['S002success-equivalence','S004actualmeanPredictlittle-o'],
    stages='draft types only; distinct actor contractreview pending',
    no_source_statement_repair=True,publication_boundary='C1/C2open,3–16unenumerated,fiveold-moduleauditsrequired,Goalactive'))
write(CONTRACT/'reader-requirements-v1.json',dict(
    math_order=['source anchor/formula','notation/index/info/AE support','displayed formula proof',
        'explicit source/Lean deltas','folded exactheaders/proofs','actual local/upstreamdeps','remainingrequiredboundary'],
    required_context=['sameinfiniteμ/Y/π','minE outsideE','seedindependentWHOLEstream',
        'legalpastonlyfeasibility','unknown-lawactualmeanPredictinitialhalf','derived4logapplication',
        'expectedordinaryzero versusadversarialupperepsilon','eventualT>0/T0difference',
        'equivalence≠arbitrarypolicyconvergence','generalkernel/completion/AEfactorization REQUIRED'],
    stable_old_registry='all previous declarationIDs/URLs/statementhashes/cards/notecontent retained',
    graph=dict(lean='new-node/integration-node only compiler actualVALUE deps when available',
        overview='ownC1bounded subobligation; original16objects/proof-totalnull/wholeC1open',
        functor='none-found-with-reason: normalizing existing causal IID excess and existing meanPredict upper; no cross-setting transport certificate'),
    site_generation='isolated tmp output only after applicable true combinedLean gate; never website/_site edits',
    no_accepted_or_merged_or_live_claim_at_draft=True))
ledger = load('docs/contracts/online-randomized-iid-v1/chapter-one-source-ledger-accepted-v3.json')
original = ledger['maintext_items']
write(CONTRACT/'chapter-one-source-ledger-draft-v1.json',dict(
    immutable_prior_ledger_sha256=sha('docs/contracts/online-randomized-iid-v1/chapter-one-source-ledger-accepted-v3.json'),
    maintext_items=original,required_proof_leaf_total=None,original_source_objects=len(original),
    own_overlay=dict(task=TASK,status='draft-only',source_obligations=['C1-EQ1.1-1.2'],
        derived_application='unknown-lawmeanPredict expected-fixed success, sourceTheorem1.3'),
    required_unclosed=['fullC1coverageaudit','fiveoldmoduleaudits','wholeC1gate','C2','C3-C16','necessaryappendices'],
    chapter_complete=False,goal_complete=False))
write(RUN/'retrieval-review-v1.md','''Actual native reference/list/query commands completed, logs retained; existing semantic retrieval may contain historical scan status and is not proof. Typed selected Mathlib/ABRL declarations independently elaborated in typed-api-search-v2.log, including axioms; original incorrect Filternamespace query failedandretained. No targetchange. MLIB-ASYMPTOTICS/MILIB-MEASURE-INTEGRAL/MILIB-REAL-LOG-SQRT actualimportcandidates. Generic center-normalization adapter reuses existing normalized_excess and Mathlib little-oiffdivision; S002/S004 are realconsumers, mathlib-candidate adapter notnewasymptoticfoundation. Theorem1.3 + empiricalMean_minimizes + expectedfixedprefixdecomposition produceupper, notsuppliedstability/independence consumer. StrictpastfeasibleAE predictionsderiveL2using meanPredict_measurable/mem; oldpointwise meanPredict_memLp deliberatelyunused. Existing NoRegret onlyeventualupperepsilon anddoesnotcloseordinaryzerolimit; separate zero proof required. All pins and priorproduction immutable.

Typographical clarification to draft contract: it says 'two actual theorem edges' as a narrative phrase; no numeric coverage or proof progress is derived from it. Precisely four frozen targets, S001 generic adapter/S002equivalence/S003derivedupper/S004actualsuccess, all currentlyUNPROVED. Original16sourceitems/proof-totalnull unchanged.
''')
write(RUN/'source-review-packet-v1.md','''Anti-anchored CONTRACT review only, distinct source_reviewer reused with disclosed history, requestedAstra/medium without runtime attestation. Freshly inspect pinned PDF13/14/16 originals and current exact four Lean Propdefs/headers, source intent/assumption ledger/DAG/conversionwindow/obligations and neutral decoder report. Compare all seven slots. Reject any hidden strengthening or substitution minE/Emin or arbitrary-policyconvergence. S003/S004 DERIVED applications of oldTheorem1.3, not new source-numbered result. S002 only bounded explicitprivate-seed model: fullsourceclass audit required. T0 genericidentity may differ; equivalence uses eventualT>0. No theorembodies yet: typedtarget/API exit0 is NOT proof. Existing sourceobjects/Goalunclosed. Only create source-contract-review-v1.md and source-contract-receipt-v1.json, hashallinputs pre/post. Return accepted/rejected/accepted-with-explicit-delta with exact repairs and scope. No BODY/FINAL/site/merge acceptance.
''')
paths = [RUN/'source-review-packet-v1.md',RUN/'blind-reconstruction-v1.md',RUN/'blind-receipt-v1.json',
    RUN/'retrieval-review-v1.md',RUN/'00_context.md',RUN/'10_director.md',RUN/'20_architect.md',
    RUN/'typed-api-search-v2.lean',RUN/'typed-api-search-v2.log']
paths += list(CONTRACT.glob('*'))
paths += [RUN/('source-pdf'+str(p)+suffix) for p in [13,14,16] for suffix in ['-text-v1.txt','-v1.png']]
paths += [Path(p) for p in load(RUN/'draft-baseline-v1.json')['fixed_files']]
assert all(p.exists() for p in paths)
write(RUN/'source-review-inputs-v1.json',dict(fixed_inputs={p.as_posix():sha(p) for p in paths},
    PDF_sha256=PDF_SHA,permissions=['source-contract-review-v1.md','source-contract-receipt-v1.json']))
print('Exact source contract review packet ready; no proof bodies authorized yet.')
