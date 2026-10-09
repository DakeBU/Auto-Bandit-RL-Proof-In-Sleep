from candidate_guard_v4 import *
candidate_fixed();actual_gates_fixed()
b=load(RUN/'formula-render-v2-browser.json');assert len(b['images'])==4 and not b['errors'] and not b['failed']
px=load(RUN/'root-original-pixel-review-v1.json')
assert px['actor']=='/root' and px['personally_viewed_original_count']==4 and px['images']==rows([RUN/n for n in b['images']])
assert load(RUN/'registry-inspected-v1.json')['total_nodes']==11055
capture('FINAL-fresh-fetch-v1','git','fetch','origin')
_,out=capture('FINAL-parent-PR215-v1','gh','pr','view','215','--json','number,url,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt')
pr=json.loads(out);assert pr['state']=='OPEN' and pr['isDraft'] and pr['mergedAt'] is None and pr['headRefOid']==BASE
_,status=capture('FINAL-canonical-research-status-v1','git','-C','E:/ABRL/research','status','--porcelain=v1','-z')
assert not status
_,main=capture('FINAL-fresh-main-v1','git','rev-parse','origin/main')
indices={sha(p):dict(path=p.as_posix(),encoding='raw-file') for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}

def walk(obj,p,at=''):
    if isinstance(obj,dict):
        for k,v in obj.items():
            if 'base64' in k.lower() and isinstance(v,str):
                try: raw=base64.b64decode(v,validate=True)
                except Exception: continue
                indices[hashlib.sha256(raw).hexdigest()]=dict(path=p.as_posix(),encoding='embedded-exact-base64',field=at+'/'+k)
            else:walk(v,p,at+'/'+k)
    elif isinstance(obj,list):
        for i,v in enumerate(obj):walk(v,p,at+'/'+str(i))

for d in [RUN,CONTRACT]:
    for p in d.rglob('*.json'):walk(load(p),p)
reviews=['contract-source-review-v2.json','body-and-canary-contract-review-v1.json','canary-BODY-review-v1.json','integration-plan-review-v1.json','candidate-git-site-plan-review-v1.json','candidate-whitespace-repair-review-v2.json','candidate-gate-binding-review-v4.json','browser-runtime-repair-review-v5.json','browser-catalog-repair-review-v6.json']
resolved=[]
for name in reviews:
    r=load(RUN/name);assert sha(r['report'])==r['report_sha256'] and sha(r['input_manifest'])==r['input_manifest_sha256']
    changes=[]
    for row in load(r['input_manifest'])['rows']:
        if sha(row['path'])!=row['sha256']:
            assert row['sha256'] in indices,(name,row)
            changes.append(dict(path=row['path'],historical_sha256=row['sha256'],current_sha256=sha(row['path']),exact_historical_snapshot=indices[row['sha256']]))
    resolved.append(dict(review=name,review_sha256=sha(RUN/name),changed_live_rows=changes,all_other_current_rows_RAW_unchanged=True))
write(RUN/'FINAL-historical-bindings-v1.json',dict(reviews=resolved,scope='Exact historical RAW recoverable. Six source integrations, bounded OWN native prior prefixes and five whitespace transitions are not described as unchanged live rows.'))
reg=load(RUN/'registry-inspected-v1.json')
write(RUN/'PR-body-v1.md','Proves Orabona v10 Lemma4.13: the cumulative right-endpoint weighted sum of a continuous nonincreasing nonnegative function is bounded by its integral. Offset0, horizon0 and zero increments are retained. This is one reusable prerequisite for Chapter2 adaptive OSD, with two full public canaries, rather than the adaptive algorithm or its regret bound.\n\nValidation: shared root9116/Tests9292; full harness retry472tests7skips and exporter;3public values/standard axioms/3frozen statements;3selected inequality VALUE calls. Both nonempty contributor bases passed. Clean local site '+reg['source_commit']+' preserves all11054oldregistryobjects +one canonical theorem=11055;15cards/18sourceMathJax/4originaldesktopimages receive root and distinctFINAL review. Genuine first harness/untracked-source, whitespace and browser failures are retained. Exact evidence: docs/contracts/online-ch2-adaptive-summation-v1 and runs/online-ch2-adaptive-summation-20261010/FINAL-review-v1.md.\n\nStacked on OPEN draft unmerged PR215 exact '+BASE+' ('+pr['headRefName']+'). Real extension outside the nonnegative half-line is unconstrained; the source nonnegativity premise remains although unused. No inverse-square-root continuity at0, attained minimum in zero-coefficient cases or algorithm conclusion is inferred. All8Chapter2forwardcontainers/6futureclaims remain required/open; Chapter2partial/null,Ch3-16unenumerated/null,wholeChapters1-16GoalACTIVE.\n\nNo merge/deployment/main/live/CI/retirement claim; local site binds its clean source commit, not later evidence heads. Worktree is retained for the next required proof package.\n')
write(RUN/'PR-plan-v1.json',dict(title='[Online Learning Ch2] Prove adaptive summation prerequisite (Lemma4.13)',body_path=(RUN/'PR-body-v1.md').as_posix(),body_sha256=sha(RUN/'PR-body-v1.md'),base=pr['headRefName'],head=BRANCH,parent_exact_head=BASE,draft=True,merge=False,deploy=False))
write(RUN/'FINAL-packet-v1.md','''# Final bounded integral prerequisite review

Independently review the exact actual Lemma4.13 source/production proof, complete two-canary statements/bodies, neutral reconstructions and all stage judgments. Search for mismatch across seven slots; no anchoring on prior favorable verdicts. Source PDF51/52 and fingerprint are pinned; originals were personally viewed in CONTRACT stage and root reread52. No new external/human/absolute-blind/model-runtime claim.

Actual final production/canary hashes are unchanged. Recheck complete public generic application, three public standard-only axiom brackets, three native fences/safe-verifies and actual compiled TYPE/VALUE evidence. Independently selected THREE canary inequality conjuncts contain the public lemma; presence is not logical necessity or a full transitive graph. Production has one actual proof, no definitions/private helpers; Test two FULL public proofs/no private helpers. Preserve source half-line regularity/nonnegative offset/prefix increments/T0/zero increments/retained unused hf. No assumed comparison or algorithm guarantee.

Check actual combinedroot9116/Tests9292 and full retry472tests7skips/exporter/checkpassed; initial failed harness/untracked source, whitespace and browser failures remain. Actual two NONEMPTY contributor outputs, OWN explicit-absent-frontier shadow, ordinary fullBASE whitespace, source/Test/root/pins unchanged. Clean-site source6c935087e7820fe6c54c4534fcd02dcfa91c72ee versus later evidence heads stays distinct. Complete11054oldregistryobjects unchanged +one source-qualified canonical theorem=11055;15sourcecards. No Test/perBook duplicate or fake adaptiveOSD proof edge. Counts are structural/display, not completed source-result/chapter denominators. Three graph contracts and six-file integration boundary remain explicit.

Personally call view_image(detail=original) on ALL FOUR current v2 ORIGINALS named in formula-render-v2-browser.json: first viewport,sourcecard,teachingnote,catalog. Inspect NL/formulas/proof/delta/open boundaries/folded exact Lean and actual wrapped COMPLETE statement/pinned proof-source link. Tall note may be resized by app; supplementary original-scale crops in root pixel receipt may be personally viewed for legibility, never substitute derivative hashes for original binding. Catalog does NOT embed proof BODY. ActualCJS/DOM geometry/errors/18sourceMathJax/four generatedRAW before-after are supporting evidence, not personal pixel review. Partialthreev1failed-capture originals remain historical, not current successful gate. LocalfileURI/1440desktop only, noHTTP/mobile/live claim.

Review FINAL-historical-bindings: every changed prior live row has exact retrievable old RAW snapshot/base64, all other rows unchanged. No normalization of retained fence/decoder/native bytes. Four NEWOWN helper EOF transitions and five literalCRLF metadata rules are separately reviewed; normal whitespace checks retained. All34991otheroldbaselineRAW and six approvedAFTER paths stay fixed. Current shared globalSGB/frontier remains unchanged.

Read BOTH complete prospective native helpers publication_guard_v1.py and record-native-acceptance-v1.py plus exact native-acceptance-plan-v1 and originalRAWsnapshot. They may execute only AFTER your favorable FINAL/all input hashes. Allow ONLY eight exact mutable OWN paths: manifest SIX listed textfields, four docs append exact suffix, native trials appendONEacceptedreview1->0ONLYone frozen production proof, events appendcandidate thenaccepted with stableID/parent/sequence/payload verification and state next+2/currententry/currentleaf. Candidate stage already has real evidence BEFORE this review; later runtime candidate append is explicitly retrospective transport, not real-time scientific enforcement. Two public canaries/zero defs/one sourcefamily separate; no sourcecontainer/chapter/Goal closure. Ownjournal,attrs,allotherFINALinputs immutable. OWNfrontier native output retained exactRAWtmp/base64 then explicitly parsed LF copy; scoped shadow must not mutate globalSGB. Actual postnative contributor/BASEwhitespace checks do not rerun Lean. Interrupted transition requires exact inspection, not arbitrary retry.

Output ONLY FINAL-review-v1.md/json. Required fields: verdict/package_verdict,required_repairs,report/report_sha256,input_manifest/input_manifest_sha256,approved_native_plan_sha256,approved_native_helper_hashes EXACT plan helpers,original_images_personally_viewed with four original path/hash bindings, semantic/visual/gate judgments and pending postnative/delivery boundary. Check every FINAL input RAW before/after, current candidate/gate guard read-only. No helper execution, native event or input mutation by reviewer. If accepted authorize only exact native helper; independent postnative review and scoped commit/nonforcepush/draftPR/officialattachment still required. All8forwards/6futureclaims required/open; Chapter2partial/null,Ch3-16unenumerated/null,wholeGoalACTIVE. No merge/deploy/main/live/retirement.
''')
capture('FINAL-stage-v1','git','add',*load(PLAN)['stage'])
changed,bindings=exact_cached_scope()
capture('FINAL-full-BASE-whitespace-v1','git','diff','--cached',BASE,'--check')
write(RUN/'FINAL-staged-scope-inspected-v1.json',dict(changed_paths=changed,all_staged_blobs=bindings,actual_full_BASE_whitespace_exit=0,scope='Exact candidate package plus OWN review proposals/evidence staged; no native acceptance/delivery.'))
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([MODULE,TEST,CONTRIBUTION,PDF,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean'])
paths.update(ROOT/p for p in OLD_ALLOWED)
paths.update(ROOT/d/(TASK+'.md') for d in ['tasks','conversion-windows','proof-obligations','research-wiki/retrieval-index'])
paths.update(ROOT/p for p in ['lean-toolchain','lakefile.lean','lake-manifest.json','website/scripts/build_site.py','website/scripts/check_site.py','tools/check_contributor_contract.py','tools/abrl_lifecycle.py'])
paths.update(Path(r['path']) for r in load(RUN/'browser-render-inspected-v2.json')['generated_inputs_before'])
paths.update(Path(r['path']) for r in px['supplemental_readonly_crop_images'])
candidate_fixed();actual_gates_fixed()
write(FINAL_INPUTS if 'FINAL_INPUTS' in globals() else RUN/'FINAL-inputs-v1.json',dict(rows=rows(paths),source_commit=reg['source_commit'],production_proof_terminals=1,new_definitions=0,public_canaries=2,source_family_count=1,source_container_closed=False,chapter_proof_total=None,chapter_complete=False,whole_Goal='active'))
print('Concrete FINAL source/gate/pixel/native-proposal packet prepared; distinct review pending.',flush=True)
