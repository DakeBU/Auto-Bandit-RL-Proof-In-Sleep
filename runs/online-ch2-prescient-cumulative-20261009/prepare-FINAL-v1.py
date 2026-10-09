from publication_guard_v4 import *
fixed()
for label in ['site-build-v2','site-check-v2','registry-command-v2','reader-file-browser-capture-command-v2','contributor-stack-v2','contributor-main-v2']:
    assert load(RUN/(label+'.json'))['actual_exit']==0,label
b=load(RUN/'formula-render-v2-browser.json')
r=load(RUN/'registry-inspected-v2.json')
binding=load(RUN/'clean-candidate-site-binding-v2.json')
assert r['source_commit']==binding['actual_head'] and r['total_nodes']==11020
assert r['retained_complete_old_nodes']==11015
assert len(b['images'])==12 and not b['errors'] and not b['failed']
assert b['actualSourceGuideMathContainers']==14 and b['url'].startswith('file:///')
for row in load(RUN/'browser-generated-inputs-before-v2.json')['rows']: assert sha(row['path'])==row['sha256']
# Execute only after root personally views all twelve repaired originals.
write(RUN/'root-reader-pixel-review-v2.json',dict(actor='/root',tool='view_image detail original',images=rows(RUN/n for n in b['images']),image_count=12,source_commit=r['source_commit'],actual_personal_inspection=True,
    observations='Personally viewed all12 repaired originals: firstviewport/sourcecard/fiveproductionnotes/fivecataloguedeclarations. Shared sum explicitly permits arbitrary natural horizon and positive played schedule without monotonicity; only the two variable corollaries impose positive horizon and played-adjacent nonincrease. Fixed interfaces permit zero horizon. Original ambiguity and failed SITEv1 evidence retained. Ordered negative terminal/movement residuals and source hypothesis delta remain readable. Source card says conditional cumulative interfaces compiled/full source run open. Exact Lean remains folded; built-in catalogue wrap shows complete frozen statements without neighbor. No visible clipping/math error in these captures.',
    limits='Actual file URI desktop1440 only; not HTTP/live/deployment/mobile/all-viewports. Distinct FINAL must personally view these originals.',chapter_complete=False,whole_Goal_status='ACTIVE'))
docs=[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','research-wiki/retrieval-index']]
mut=[CONTRIBUTION,*docs,*[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','trials.jsonl','own-artifact-journal.md']]]
write(RUN/'pre-FINAL-own-metadata-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in mut]))
c=load(CONTRIBUTION)
c['graph_contribution']['visual_review']='Actual selected7public/7total nodes,1885coalesced direct TYPE_VALUE presences;8production and5canary VALUE pairs plus4independently selected Eq.mpr numeric branches retain specific new production constants. Shared registry11015complete old records unchanged+5canonicalproduction=11020. Actual local-file desktop14formulas/zeroerrors/12root-reviewed repaired originals; distinct FINAL pending. Not fulltransitive/source/coverage denominator.'
c['verification']['site_build']='Actual clean isolated repaired SITEv2 build exit0 at '+r['source_commit']+' after applicable full combined Lean gate. Pure13field reader repair; Lean/fullharness inputs unchanged. No generated _site editing/later-head fresh build/deployment/live claim.'
c['verification']['site_check']='Actual SITEv2 check/registry exit0;11015complete old records unchanged+5production nodes, no Test/generated-Test/perBook duplicates. Actual local-file browser14sourceguide formulas/zeroerrors/desktop geometry/foldedLean/builtin catalogue wrap and12root-inspected originals;4generated inputs unchanged. Distinct FINAL separate.'
c['verification']['independent_review']+=' Reader hypothesis ambiguity found after prior favorable plan review; exact13field prose repair separately accepted before write, original evidence retained. Repaired site and root pixels passed; distinct FINAL/native/delivery pending.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
suffix=('\nIntegrated reader candidate: clean isolated repaired SITEv2 at '+r['source_commit']+', actual check/shared registry11015old+5new=11020, two nonempty contributor bases. Local file desktop14formulas/zeroerrors/12root-inspected originals/4generated inputs unchanged. Original reader ambiguity and13field distinctly reviewed prose-only repair retained. Complete Lean/fullharness inputs unchanged. Full source hypothesis/valid-run transport and all8Chapter2forwards REQUIREDOPEN; Chapter2partial/null, whole16GoalACTIVE. FINAL/native/delivery pending.\n')
for p in docs:p.write_bytes(p.read_bytes()+suffix.encode('utf8'))
write(RUN/'memory-digest-v3.md','# '+TASK+'\n\n'+(RUN/'memory-digest-v2.md').read_text(encoding='utf8')+suffix+'\nOWN whitespace repair preserves exact before RAW and removes one trailing space only. Stage-v3 helper DID execute scoped add then failed missing baseline-v2 before diff-check; stage-v4 corrected pinned filename, actual full diff0. Never describe the failed helper as wholly unexecuted. Native conversion window was materialized late, never retroactive stabilization evidence. Eq.mpr is actual numeric branch head, correcting earlier packet Eq.mp. No single-runtime/fullsource/chapter/Goal/merge/live claim.\n')
event('integrated-candidate-native-v1','candidate',dict(scope='Only5conditionalsame-run cumulative proofs/2fullpubliccanaries; fullsourceOPEN',full_harness_sha256=sha(RUN/'full-harness-inspected-v1.json'),site_check_sha256=sha(RUN/'site-check-v2.json'),registry_sha256=sha(RUN/'registry-inspected-v2.json'),browser_sha256=sha(RUN/'formula-render-v2-browser.json'),root_pixels_sha256=sha(RUN/'root-reader-pixel-review-v2.json'),FINAL_pending=True,chapter_complete=False,goal_complete=False))
indices={sha(p):dict(path=p.as_posix(),encoding='raw-file') for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
def walk(obj,p,at=''):
    if isinstance(obj,dict):
        for k,v in obj.items():
            if k in ['raw_base64','historical_raw_base64'] and isinstance(v,str):
                raw=base64.b64decode(v);indices[hashlib.sha256(raw).hexdigest()]=dict(path=p.as_posix(),encoding='embedded-exact-raw-base64',field=at+'/'+k)
            else:walk(v,p,at+'/'+k)
    elif isinstance(obj,list):
        for i,v in enumerate(obj):walk(v,p,at+'/'+str(i))
for d in [RUN,CONTRACT]:
    for p in d.rglob('*.json'):walk(load(p),p)
resolved=[]
for name in ['contract-review-v1.json','first-leaf-BODY-review-v1.json','three-BODY-canary-CONTRACT-review-v1.json','five-BODY-review-v1.json','publication-plan-review-v1.json','publication-plan-review-v2.json','publication-plan-review-v3.json','reader-scope-triage-v1.json','reader-scope-plan-review-v1.json']:
    changes=[]
    for row in load(RUN/name)['raw_input_checks']:
        p=Path(row['path']);old=row.get('before_sha256') or row.get('expected_sha256') or row['sha256']
        if sha(p)!=old:
            assert old in indices,(name,p,old)
            changes.append(dict(path=p.as_posix(),historical_sha256=old,current_sha256=sha(p),exact_historical_snapshot=indices[old]))
    resolved.append(dict(review=name,review_sha256=sha(RUN/name),changed_live_rows=changes,all_other_current_inputs_unchanged=True))
write(RUN/'FINAL-historical-binding-resolution-v1.json',dict(reviews=resolved,scope='Exact before bytes for approved historical proof/native/OWN metadata/five publication paths and13field reader repair. Historical reviews are historical, not assertions current live rows stayed unchanged.'))
stage=load(RUN/'candidate-stage-plan-v4.json')['stage']
capture('FINAL-stage-v1','git','add',*stage)
capture('FINAL-full-package-diff-v1','git','diff','--cached',BASE,'--check')
write(RUN/'FINAL-diff-audit-v1.json',dict(actual_full_exit=0,current_package_RAW_exceptions=[],no_production_Test_reader_contract_exemptions=True,distinct_FINAL_pending=True))
capture('FINAL-parent-PR211-v1','gh','pr','view','211','--json','number,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt,url')
write(RUN/'FINAL-packet-v1.md','''# Five conditional same-run cumulative proofs FINAL

Independently review all5 actual frozen production bodies and both complete16/22conjunct canaries. Common actual Option iterate, hseq throughT, all actual states interiorX, actual derivatives from differentiability; each played extendedloss SourceProper and global ambient supports at ALL feasible points. Whole current loss is read before paid successor, no future/comparator/desiredregret input. Sum derives actual one-step then divides positiveplayed steps. ArbitraryTincl0 and arbitrary positiveplayed schedule, no monotonicity/M/MAX for this interface. Fixed sharp telescopes actualx(0)=x0, preserves negative terminal and all movements, permitsT0. Variable sharp T>0/positivebeforeT/nonincreaseonlyt+1<T uses canonical weighted_potential_sum witha2B/C2M andM arbitrary real; previousstatebounds only. Both printed corollaries add VsubsetX/StrictConvexOn to derive terminalnonneg, droponlynegative terminal, retainmovements. FiniteMAX precisely states0..T-1; etaTunused.

Canaries V[-1,1], psi=z4/4+z2/2, actualstates.5->0->.5. Fixed losses restrictedabs then-5z/8/step1: movements11/64,9/64, terminal5/8, full16conjunct with universal three newbounds and separatelyselected numeric-9/8<=-5/16, -9/8<=5/16. Decreasing1,.5 has genuinely newloss-5z/4 and actual unique penalizedminimum via polynomialfactorization; full22conjunct, weightedmovement29/64, previousMAX at-.5=5/8/at+.5=9/64 versus initial0, newvariablesharp/printeduniversal and numeric-7/4<=-29/64,-1/2<=-11/64. Four individually selected actual compiled numeric branches have Eq.mpr heads and corresponding newtheoremVALUE constants, not wholeconjunction-only membership. No theorem unfolding/proofirrelevance normalization.

Pinned source v10 PDF277/278/265-266, Definition6.4 PDF75. Source closed generator onX/finiteEuclidean, Vnonemptyclosedconvex, x0/actualstatesinterior, proper extended losses/subdiff onV. Current reusablecompleteHilbert/ambientrepresentative/globalproper-support/actualsuccess-hseq interfaces are explicitly conditional derived progress. Full sourceX/interior generator representation/closedness packaging, finite-onV/noBottom proper/global-support transport and validrun wrapper remain REQUIREDOPEN. Not sourceerratum/unconditional attainment/completeAlgorithm15.8/T15.30/Chapter6/15 acceptance/Chapter2 closure. All8Chapter2forwardsOPEN, Chapter2partial/denominatornull, Ch3-16unenumerated/null, whole16GoalACTIVE. Maintext fixed exercise is not skipped: its conditional interface is proved here, fullsourcehypothesis wrapper OPEN.

Review distinct neutralproduction/canary reconstructions and CONTRACT/BODY/plan/repair records, not compilation alone. Earlier Eq.mp packet typo corrected by actualEq.mpr receipts. Delayed conversion artifact explicitly did NOT exist at stabilization: draft intent existed, actualnativeconversion materialized onlyafterapprovedplan, exact contemporaneousbefore/session-journal audit. Earlier recovered historical RAW bindings labeled recovered, not contemporaneous. Failed ppExpr/nativekind/proofsup'/numericAnd.casesOn attempts and equivalent repairs preserved, no frozen target weakening.

Reader original SITEv1 had apparently valid DOM/math but root found scope ambiguity; independenttriage required13field repair. Exact plan separatelyreviewed before writes. Onlynewnote plain/lean_notes10fields/newcard plain/fallback/contract.assumptions3fields changed; sourceformula/body/header/link/oldfields unchanged. Old favorable review and originalDOM/12pixels preserved. Current repaired SITEv2 onlyacceptedafterfresh registry/check/browser/root/distinct pixels. Current firstsum explicitly allowsT0/arbitrarypositive schedule; variable-sharp/printed alone requireT>0 and played-adjacent monotonicity.

Actual public5production+2fullcanary VALUEs,7standardonly axiomlists (propext/Classical.choice/Quot.sound),7rawheaders/nativefences; selected7public/7total nodes/1885coalesced directTYPE_VALUE presences,8requiredproduction/5requiredcanaryVALUEpairs/fourselectednumerictails. Not fulltransitive/occurrence/source/registrydenominator. Actual focused builds and combinedroot9112/Tests9284cachedinclusivejobs; fullharness472tests/7existingskips/actualcompiler/exporter/checkmarkers in inspected/raw receipts. Commands exit0 alone notcompiled. Frozen source/Test/root/pins unchanged after fullgate; later13readerprose fix does not rerunfullharness, no freshfullharness-at-latersitehead claim.

Native OWNmetadata only; globalSGB/journal/indexes unchanged. Actual scopedrealCLI reference-index eight outputs/production5present/Testseparate. OWNshadowmismatches[]/would_mutatefalse. Two nonempty contributor bases. Exactly5oldbaselinepaths only (root/Testimports, online-ogd module/goal/completionsuffix,1card,5notes). All32923otheroldpaths preserved byguard. All11015complete old registry objects unchanged+5canonicalproduction=11020, noTest/generatedTest/perBookduplicates; sourcecards11. Clean isolated repairedSITEv2 sourcecommit bound in clean-candidate-site-binding-v2, no later-evidence-head freshsite/live claim. Generatedwebsite/_site notedited.

Whitespacefailure: oneOWN trailing space removed, exactORIGINAL RAW/base64 preserved; nootherbytes changed. Stage-v3 helper DIDexecute scopedadd then failed FileNotFound baseline-v2 before diff; correctedexplicitstage-v4 pinnedbaseline-v1 actualfull diff0. Prospective helper creation log word unexecuted was imprecise; do not repeat it. RAW/GitCRLF differences preserved exactly, no JSONreserialization substitutions. Historicalreview changedlive rows must resolve exactbeforebytes via FINAL-historical-binding-resolution-v1, not falsely unchanged. Independently guard/rehasheveryFINAL RAWbefore/after.

Personally view ALL12 CURRENT ORIGINALS from formula-render-v2-browser.json with view_image detail original: viewport/card/5notes/5catalogues. Rootviewingdoesnotdischargeyours. Actual fileURI desktop1440/14sourceguideMathJaxcontainers/zeroerrors/foldedLean/built-inwrap/4generatedinputsunchanged; notHTTP/live/mobile/allviewports. No rejectedHTTPservice retry.

Create-only FINAL-review-v1.md/json with report/inputsha/rawbeforeafter/personal12pixelsha and separate semantic/proof/canary/reader/registry/visual/scope/package verdicts/requiredrepairs. Distinct reused staged automated actor/history disclosed/requestedAstra-medium, no human/external/absolute-blind/runtimeattestation. Approve only bounded5proofs/2fullcanaries, not fullsource/chapter/Goal. Allowed subsequentexistingOWNmetadata: contribution semantic_roundtrip.remaining_semantic_delta,verification.independent_review,graph_contribution.visual_review ONLY; OWNtask/proofobligations/retrievalsuffixes; OWNnative trial/session/state/journal permitted byactualCLI. Newmemory/postnative/delivery evidence may becreated. Production/Test/root/reader/source/contracts immutableafterFINAL. Native5->0 countsONLY5frozenproofs, then distinctpostnative/actualdeliveryreviews. Scopedcommit/push/draftPR stacks on OPENdraftunmerged PR211 exact24de0231aa067f141251aac5c20deb58e448ea66, branchcodex/research-online-ch2-prescient-causal. No merge/deploy/retirement/main/live/CI claim.
''')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([PUBLIC,CANARY,CONTRIBUTION,PDF,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',*docs,ROOT/'conversion-windows'/(TASK+'.md')])
paths.update(ROOT/p for p in ['lean-toolchain','lakefile.lean','lake-manifest.json','website/scripts/build_site.py','website/scripts/check_site.py','tools/check_contributor_contract.py','website/content/chapters.json','website/content/readings.json','website/content/highlights.json'])
paths.update(Path(row['path']) for row in load(RUN/'browser-generated-inputs-before-v2.json')['rows'])
fixed()
write(RUN/'FINAL-inputs-v1.json',dict(rows=rows(paths),source_commit=r['source_commit'],phase='Distinct bounded FINAL; native/delivery pending',production_proofs=5,new_definitions=0,public_canaries=2,generated_Test_auxiliaries=0,new_registry_nodes=5,chapter_proof_total=None,chapter_complete=False,whole_Goal_status='ACTIVE'))
print('Exact repaired FINAL packet ready; distinct review pending.')
