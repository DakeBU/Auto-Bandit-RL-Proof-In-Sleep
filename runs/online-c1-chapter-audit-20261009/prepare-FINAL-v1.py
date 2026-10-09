from common_reader_v6 import *

fixed()
capture=load(RUN/'formula-render-v2.json')
write(RUN/'root-reader-pixel-review-v2.json',dict(actor='/root',
    personally_viewed_current_original_files=capture['images'], image_count=10,
    source_commit=capture['source_commit'], actual_tool='view_image detail original; tool display resized tall images',
    observations='All ten current files personally viewed. Readable rendered formulas and complete wrapped public types. Positive horizon, unit-prefix/all-time hypotheses and TRUE-best versus fixed-comparator metrics are explicit. Upper semantics are not ordinary limits; source reconciliation is explicitly a proposal. Exact Lean is initially folded; built-in wrap reveals all four catalogue types. No visible clipping or horizontal overflow in these desktop images.',
    scope='1440px desktop capture only; no physical-device or all-viewports claim',
    current_DOM_report_sha256=sha(RUN/'formula-render-v2-browser.json'),
    recovery_receipt_sha256=sha(RUN/'capture-output-recovery-v2.json'),
    independent_FINAL_pending=True, chapter_complete=False,goal_complete=False))
write(RUN/'memory-digest-candidate-v3.md', '''Four actual general-initial FTL terminal proofs and 27 complementary canary bodies retain all frozen headers and distinct BODY review. Actual combined root 9105, Tests 9270 and full harness 472 tests/7 skips passed; standard-only axioms, native fences, direct VALUE evidence and own shadow are separate evidence. Current source17 integration remains candidate: 54 generic contracts, 27 canaries and null required proof-leaf total are different quantities. Registry preserves all10977 old nodes plus4 exact shared public theorem nodes, one newly discharged source family. Current clean SITE3 source78482 passed build/site/registry and both nonempty contributor bases. ROOT viewed10 current desktop images; distinct FINAL/native/postnative/delivery remain required.

Failures preserved: proof-body tactic/cast failures; route1-4 schema repair; contributor affected-files schema repair; current capture v3 missing old lookup and v4 postprocessing filename collision. Actual Node0 v4 outputs were preserved v2 and historical v1 bytes restored exactly by known SHA; failed wrapper1 is not recast passed. Cumulative diff retains exactly11 old SHA-bound RAW exceptions (9 logs and2 frozen decoder reports), scoped production/Test/readers/contracts have none; independent FINAL must adjudicate.

Pinned ordinary-limit definition, false universal inference, actual same-FTL dyadic obstruction, conditional empirical-mean equivalence, upper no-regret and TRUE-best average0 remain distinct. IID fixed comparator minimum is outside expectation, with actual jointIID/strictpast/private-tape/AE legal model; kernel and completed variants retain explicit subordinate models. Derived1/6 lower constant is not printed/sharp/samplewise. Legal initialized FTL rising0,1 has positivebest1/2 and firstcorrection-1/4; earlier false reviewer example is separately corrected. Whole1-16Goal ACTIVE, C2partial/C3-16unenumerated/null/appendicesrequired; old source16/contracts50/oldBook links/pins/globalSGB/private/frozen/generated paths preserved. Current stacked dependency PR202 a03f OPENdraft unmerged; no merge/main/live/retirement.''')
historical=load(RUN/'chapter-canary-BODY-inputs-v2.json')
by_hash={sha(p):p for p in (RUN/'snapshots').rglob('*') if p.is_file()}
changes=[]
for old in historical['rows']:
    p=Path(old['path'])
    if sha(p)!=old['sha256']:
        snapshot=by_hash.get(old['sha256']);assert snapshot,('Missing historical exact snapshot',p)
        changes.append(dict(path=p.as_posix(),historical_sha256=old['sha256'],
            exact_historical_snapshot=snapshot.as_posix(), current_sha256=sha(p)))
assert len(changes)==5
write(RUN/'FINAL-historical-binding-resolution-v1.json',dict(
    original_BODY_index_sha256=sha(RUN/'chapter-canary-BODY-inputs-v2.json'),
    original_count=925, unchanged_current=920, changed_live_rows=changes,
    reason='Approved exact Tests append, current reader/coverage snapshots, and own proof-export journal append. Old bindings resolve to exact preserved snapshots; they are not claimed live-identical.'))
gate('FINAL-stage-evidence-v1','git','add',RUN.relative_to(ROOT).as_posix())
code=gate('FINAL-cumulative-full-diff-v1','git','diff','--cached',BASE,'--check',required=False)
exceptions=load(RUN/'candidate-diff-audit-v2.json')['retained_exact_RAW_exceptions']
allowed={Path(x['path']).relative_to(ROOT).as_posix():x['sha256'] for x in exceptions}
observed=set()
for line in (RUN/'FINAL-cumulative-full-diff-v1.log').read_text('utf8').splitlines():
    if ': trailing whitespace.' in line or ': new blank line at EOF.' in line:
        p=line.split(':',1)[0];assert p in allowed,p;assert sha(ROOT/p)==allowed[p];observed.add(p)
assert observed==set(allowed) and code==2
gate('FINAL-cumulative-scoped-diff-v1','git','diff','--cached',BASE,'--check','--','.',*[':(exclude)'+p for p in sorted(observed)])
write(RUN/'FINAL-cumulative-diff-audit-v1.json',dict(base=BASE,
    actual_full_exit=code, exact_RAW_exceptions=exceptions, exception_count=len(exceptions),
    exact_log_count=sum(Path(x['path']).suffix=='.log' for x in exceptions),
    frozen_decoder_report_count=2, scoped_actual_exit=0, full_unexcluded_gate_zero=False,
    code_reader_contract_Test_exceptions=False, distinct_FINAL_adjudication_required=True))
write(RUN/'FINAL-delivery-state-v1.json',dict(
    actual_HEAD=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip(),
    canonical_main=subprocess.check_output(['git','-C','E:/ABRL/research','rev-parse','HEAD'],encoding='utf8').strip(),
    fetched_origin_main=subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf8').strip(),
    canonical_status=subprocess.check_output(['git','-C','E:/ABRL/research','status','--porcelain'],encoding='utf8'),
    PR202=json.loads(subprocess.check_output(['gh','pr','view','202','--json','number,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt,url'],encoding='utf8')),
    worktree_kept_active=True, new_PR_pending=True, merge_deploy_authorized=False))
write(RUN/'FINAL-review-packet-v1.md', '''# Distinct Chapter1 FINAL integration review

Review the entire pinned Chapter1 maintext integration, NOT just four new proofs or27 canaries. Use current FINAL-inputs-v1.json; independently hash all current RAW rows before and after. Reuse earlier staged source pixel inspection only with exact fingerprints and disclose actor history. Personally view all10 CURRENT v2 screenshot files from formula-render-v2.json with view_image; v1 ROOT inspection does not discharge your current review. Requested GPT6Astra/medium, no runtime/human/external/absolute-blind attestation. Same staged reviewer and blind decoders are distinct from formalizer.

Inspect actual source PDF13-19/printed1-7, source-map-draft-v3/current-candidate-v4 all17 source audit objects, exact50+4 public terminal headers/definitions, old50/current4 values, canary27 values, actual direct VALUE/axiom/fence evidence, all separate BODY/CONTRACT verdicts and v4 correction, current reader-integration bindingsv3/proposal/scopev4 and generated SITE3. Assess seven semantic slots for ALL17 and R1-R10 from source-contract-review-v3. The qualitative lower and IID benchmark require actual producers and precise quantifier/expectation models, not consumer oracles. Original16 retained verbatim, seventeenth general-initial family is mandatory and now actualproofs. Four newpublic proofs are one source family; generic54/canary27/null total are not percentages. Chapter1 source-object count is17, not a book theorem/proof denominator.

Key deltas remain explicit: source literal ordinary finite comparator limit is frozen; actual same halfFTL dyadic stream disproves its universal inference. Upper-epsilon no-regret, TRUE-best average0, conditional mean-convergence iff and proposed source correction remain separate, with no author endorsement or false theorem claim. Decide whether this honestly discharges the chapter as formal source/correction integration; do not delete a difficult or false source obligation. Unit squared-loss has no half. Source half quarter-plus-tail/4+4log remains; legal ANYinitial now1+tail with exactfirstcorrection;5+4log is derivedproofintermediate only. Rising0,1 initial0 truebest+1/2 and correction-1/4; v3 reviewer false negative example separately withdrawn. T0 empty, firstcorrection positive-horizon only. Unknown-law learner is actual strictpastmean/state, not populationoracle. IID expected FIXED min is outside expectation; jointIID/strictpast/independententireprivatetape/AE unit/completed/kernel models explicit. Kernel stream exogenous, no unspecified actionresponsive/sideinformation universality. Lower1/6 is derived expectedseed fixedbinarywitness, not sourceconstant/sharp/samplewise/highprob. W-output/V-comparator/general explicitloss typing, suppliedargmin Lemma1.2 versusproducedempiricalminimum/uniqueness/T0ties, actualemptytransition/countmean/ideal arithmetic no bitcost are covered.

Actual combined Lean root9105/Tests9270/fullharness472tests7skips checkpassed applies unchanged exactcode/pins. Separately current clean SITE3 build/sitecheck/registry0 preserves10977 fullold nodes plus4publictheorems, no newproductiondefs/privatehelpers orTestcanonicalnodes. Current two NONEMPTY contributor bases both cover PUBLIC; ownshadow0; currentROOT10pixel inspection is not your inspection. SOURCE STATUS, LEAN compilation, semantic fidelity, chaptergate, merge/live remain independent.

Historical925 bindings:920 unchanged live,5 approved changes resolved by exact snapshots in FINAL-historical-binding-resolution-v1; don't assert all925 liveunchanged. Capture adapter v4 OVERWROTE OWN v1 report/DOM accidentally, caught and restored byteexact after preserving currentactualNode0 outputs. Failedwrapper1 retained; separately executed recovery0 validates currentoutputs. Historical10images unchanged, current10different hashes. No fake beforebyte snapshot; actualwrapperbeforeafterHTMLguard succeeded prior to postprocessingerror. Examine recovery and currentDOM/provenance.

Cumulative gitdiff BASE stagedfull actual2, exactly11 preserved oldRAW exceptions:9logs and2frozenrevieweddecoderMD EOFblanklines. Scoped production/Test/readers/contracts actual0; newincremental0 is NOTfullPR0. Decide explicitly whether these exactSHA preservation exceptions are acceptable; no blanket whitelist or normalization of reviewed evidence.

All original production/pins/oldTest/globalSGB/frontiers/trials/memory/retrieval, unrelatedBook rows and oldreaderrecords/history immutable except exactly reviewed ROOT/Test appends and4boundedreaders. Main clean6847, PR202 OPENdraft exacta03f stackedbase. Current own task/obligations retain template/historical stale stages; no chapter acceptance yet. Current native/trials/session need postFINAL bounded transition, not retroactive fake enforcement. Command0/compiled/semantic/accepted/PRready are different. Paper title/private/frozen/_site untouched; sharedregistry only.

Write ONLY FINAL-review-v1.md and FINAL-receipt-v1.json. Verdict accepted|accepted-with-explicit-delta|rejected; per17 object decisions, allseven slots, R1-R10, currentreader/current10personallyviewedimage hashes, evidence/failure/cumulativeRAW exceptions and remaining blocking repairs. You may reuse prior exact BODY analysis, disclose this; independently examine integration differences, do not claim fresh fullaudit of every dependency file. Bind index/report/currentcode/readers/exactsource. State precise permissions for postFINAL metadata only: own task/proof-obligations/conversion-window/RUN native trials/session/journal/retrieval/memory, new versioned source17 acceptance ledger, C1only coverage/currentreader status text, OWN contribution verification/semantic status. No math/header/source/oldrecords/otherBooks/globalfrontier edits. Any chapter status remains conditional until actual native/shadow/postnative/site ifreaderchanges and push/newdraftPR/attachment/delivery checks. Currentreview can approve source17 reconciliation with explicitcorrection, not whole16Goal or main/live. Request separate postnative adjudication if needed. WholeGoal remains ACTIVE regardless.
''')
paths={Path(x['path']) for x in historical['rows']}
paths.update(p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
paths.update([PUBLIC,CANARY,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',CONTRIBUTION])
paths.update(Path(r['path']) for r in load(RUN/'reader-integration-bindings-v3.json')['rows'])
paths.update(ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows'])
paths.update([SITE/'chapters/online-foundations/index.html',SITE/'books/registry.json',SITE/'site-manifest.json'])
paths.update(SITE/p for p in load(RUN/'registry-v3.json')['module_HTML_sha256'])
assert all(p.is_file() for p in paths),[p.as_posix() for p in paths if not p.is_file()]
write(RUN/'FINAL-inputs-v1.json',dict(phase='distinct full Chapter1 integration FINAL; postnative/delivery pending',
    rows=rows(paths),whole_Goal_active=True, source_objects=17, generic_contracts=54,canaries=27,proof_total=None))
fixed()
print('FINAL packet ready',len(paths),'current RAW inputs; exact11 historical diff exceptions; distinct current10pixels required.')
