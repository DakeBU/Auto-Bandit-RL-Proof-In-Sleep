from publication_guard_v1 import *
fixed()
b=load(RUN/'formula-render-v1-browser.json');assert len(b['images'])==14
write(RUN/'root-original-pixel-review-v1.json',dict(actor='/root',method='Each of14actual original PNGs personally viewed with view_image detail original',images=rows(RUN/f for f in b['images']),
    findings='All source/notation/assumption/proof/dependency/boundary blocks readable; fixed and variable formulas show negative movements and correct last played denominator/previous-state maximum. Exact Lean remains folded on teaching panels; catalogue built-in wrap has no clipping. Canonical-route compiled status explicitly differs from textbook-chapter completion.',
    transport='Actual local file URI desktop1440; no HTTP/live/mobile/all-viewports claim',independent_review_pending=True))
write(RUN/'pre-FINAL-contribution-v1.json',dict(path=CONTRIBUTION.as_posix(),sha256=sha(CONTRIBUTION),before_raw_base64=base64.b64encode(CONTRIBUTION.read_bytes()).decode('ascii')))
c=load(CONTRIBUTION)
c['verification']['site_build']='Applicable combined Lean gate passed before clean local SITEv1 build at '+load(RUN/'clean-candidate-site-binding-v1.json')['actual_head']+'. Exact source/root/toolchain hashes bound. No generated website/_site edits, deployment or later-evidence-head fresh-site claim.'
c['verification']['site_check']='Actual site check, complete11020oldregistryobjects unchanged+6canonicalproduction=11026,12sourcecards; actualfile desktop15sourceguideformulas/zeroerrors/foldedLean/wrap/14originals personally viewed byroot. Distinct FINAL/pixels pending.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
indices={sha(p):dict(path=p.as_posix(),encoding='raw-file') for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
def walk(obj,p,at=''):
    if isinstance(obj,dict):
        for k,v in obj.items():
            if k in ['raw_base64','historical_raw_base64','before_raw_base64'] and isinstance(v,str):
                raw=base64.b64decode(v);indices[hashlib.sha256(raw).hexdigest()]=dict(path=p.as_posix(),encoding='embedded-exact-raw-base64',field=at+'/'+k)
            else:walk(v,p,at+'/'+k)
    elif isinstance(obj,list):
        for i,v in enumerate(obj):walk(v,p,at+'/'+str(i))
for d in [RUN,CONTRACT]:
    for p in d.rglob('*.json'):walk(load(p),p)
resolved=[]
for name in ['contract-source-review-v1.json','six-BODY-review-v1.json','publication-plan-review-v1.json','publication-helper-review-v1.json']:
    changes=[]
    for row in load(RUN/name)['raw_input_checks']:
        p=Path(row['path']);old=row.get('before_sha256') or row.get('expected_sha256') or row.get('sha256')
        if sha(p)!=old:
            assert old in indices,(name,p,old)
            changes.append(dict(path=p.as_posix(),historical_sha256=old,current_sha256=sha(p),exact_historical_snapshot=indices[old]))
    resolved.append(dict(review=name,review_sha256=sha(RUN/name),changed_live_rows=changes,all_other_current_inputs_unchanged=True))
write(RUN/'FINAL-historical-bindings-v1.json',dict(reviews=resolved,scope='Historical reviewed stage bytes are historical; exact snapshots/recovered RAW are identified. No claim those live OWN/native paths remained unchanged across later approved stages.'))
capture('FINAL-fresh-fetch-v1','git','fetch','origin')
_,out=capture('FINAL-parent-PR212-v1','gh','pr','view','212','--json','number,url,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt')
pr=json.loads(out);assert pr['state']=='OPEN' and pr['isDraft'] and pr['mergedAt'] is None and pr['headRefOid']==BASE
capture('FINAL-canonical-research-status-v1','git','-C','E:/ABRL/research','status','--porcelain=v1','-z')
capture('FINAL-fresh-main-v1','git','rev-parse','origin/main')
write(RUN/'PR-body-v1.md','Derives properness from the source loss domain, proves strict convexity and uniqueness of each penalized minimum, and identifies valid source argmin updates with the same current-loss Option recursion. Both printed fixed and nonincreasing-step bounds then follow without an assumed successful-trajectory identity or desired one-step regret bound. Negative movement terms and the previous-state finite maximum are preserved.\n\nTwo complete public canaries use constrained nonsmooth/affine losses, a nonquadratic generator, actual states1/2 ->0 ->1/2, and fixed/genuinely decreasing steps. Each separately selected numeric proof branch retains its specific new source regret theorem. Validation includes eight public VALUEs/frozen statements/standard-only axiom lists, combined root/Tests, full harness (472tests,7existing skips), own retrieval/shadow and nonempty contributor checks against both bases. A clean local site preserves all11020oldregistryobjects and adds6canonicalproofs;14actual desktop originals receive root and distinct staged automated review. Exact failed attempts and RAW history remain recorded.\n\nStacked on OPEN draft unmerged PR #212, exact547137ea02c59c24424e2fb448174875845fadb4, branch codex/research-online-ch2-prescient-cumulative. These six proofs transport source hypotheses and actual valid runs; they do not assert universal attainment, automatic interior preservation, or an executable/measurable optimizer. Closedness/strictness alone do not guarantee attainment. All eight Chapter2 forward containers remain required/open pending dedicated reconciliation; Chapter2 and the persistent Chapters1-16 Goal are incomplete. No Chapter15 acceptance, merge, deployment, main/live or CI claim. The site applies to its bound candidate commit, not later evidence commits.\n\nEvidence: docs/contracts/online-ch2-prescient-source-v1; runs/online-ch2-prescient-source-20261010/FINAL-review-v1.md and bound receipts; research-wiki/contribution-contracts/ONLINE-CH2-PRESCIENT-SOURCE-20261010.json. Functor audit: none-found-with-reason.\n')
write(RUN/'PR-plan-v1.json',dict(title='[Online Learning Ch2] Derive source-valid prescient Bregman runs and regret',body_path=(RUN/'PR-body-v1.md').as_posix(),body_sha256=sha(RUN/'PR-body-v1.md'),base=pr['headRefName'],head=BRANCH,parent_exact_head=BASE,draft=True,merge=False,deploy=False))
write(RUN/'FINAL-packet-v1.md','''# Six source transports and two full canaries FINAL

Independently review exact actual six frozen source-loss/source-update proof bodies, both FULL8/6conjunct canaries, pinned v10 source and seven-slot semantics, staged neutral/CONTRACT/BODY/plan/helper receipts and historical binding resolver. Six scopes differ: arbitrary E properness; real inner-product strict objective with arbitrary center/no completeness; complete-space uniqueness and actual recursion identity; finite-dimensional source closed/interior/domain/no-bottom/global-support wrappers. Static generic fderiv algebra at an arbitrary center is not source Bregman validity at a bad base. Actual supplied feasible minima plus uniqueness identify the classical selector; induction proves actual SAME recursion identity, not an hseq input or a future-aware algorithm existence oracle.

Fixed natural T including0/constant positive eta. Variable T>0/positive played steps/monotonic onlyt+1<T; max overprevious states0..T-1, denominatorlastplayedeta(T-1). Both printed endpoints retain negative movements, no added terminal term; sharp parents stay distinct. Source generator represented on X by ambient representative plus extendedIndicator; closedness retained literally though not used to infer existence. Comparator may be boundary; initialcenter need not lie inV or lossdomain. No universal attainment or automatic interior preservation. Separate reviewed classification corrects historical draft unconditional-choiceability wording, not source erratum or deletion of a hard source theorem. The fixed source proof left as exercise is included.

Nonquadratic psi=z4/4+z2/2,V[-1,1],actualstates.5->0->.5. Fixed restrictedabs then-5z/8,step1,full8conjuncts: newproper/strict/actualadvance/actualiterate/universalnewfixed, movements11/64,9/64 and numeric-9/8<=5/16. Decreasing restrictedabs then-5z/4,steps1,.5,full6conjuncts: newactualidentity/universalnewvariable, weightedmovements29/64, previousMAX5/8 at-.5 and9/64 at+.5, numericat+.5 -1/2<=-11/64. Actual minima/derivative facts reused from complete parent concrete runs. No circular production dependence. Two individually selected numeric Eq.mpr proof branches retain the corresponding NEW source endpoint. Not wholeconjunction-only membership/proofirrelevance/unfolding. Canarydraftv1 wrong sharp-vs-printed numeric interface rejected; correctedv2 BEFOREstabilization/bodies. Production never weakened. All failures preserved.

Actual eight public/total selected values,1431coalesced directTYPE_VALUE presences,20requiredVALUEpairs/two selectednumeric proof dependencies; eight standard-only axiom lists/eight native fences/safeVerify. Root9113/Tests9286cached-inclusivejobs, fullharness472tests/7existing skips/230.433sec with actual compiler/exporter/check markers. Commandexit0 alone not compilation. Exact production/Test/root/pins unchanged since gate. Own actual reference-index8outputs/lookup/shadow, globalSGB/index/journal unchanged. Exact fiveoldpath publication plan, allother33442oldRAW unchanged. Sourcecompiled six proofs are not six printed source results or chapter denominator. All8Chapter2forward containers required/open, Chapter2partial/null, Ch3-16unenumerated/null; whole16GoalACTIVE.

Clean local SITEv1 candidate7be6929fb3a5ea8306fce0ebf41f3aec03fa3179, actual site check, all11020completeoldregistryobjects unchanged+6canonicalproduction=11026; no Test/generatedTest/perBookduplicates.12sourcecards. Personally view ALL14CURRENT ORIGINAL PNGs listed in formula-render-v1-browser.json with view_image detail original, and bind each hash. Rootviewing does not discharge yours. Desktop1440 actualfileURI/15sourceguideMathJaxformulas/zeroerrors/foldedLean/built-inwrap/4generatedinputsunchanged; notHTTP/live/mobile/allviewports. No rejectedHTTPservice retry. No freshsite-at-later-evidence-head claim.

Review prospective record-native-acceptance-v1.py as a separate narrow metadata step: only after favorable bounded FINAL, exact FINAL report/input hashes and all RAWinputs are rechecked. It creates own trial6->0 onlysixfrozenproofs, one accepted event/exact state transition; journalunchanged; only OWN contribution three named text fields and OWN proof-obligations/retrieval suffixes may change. Exact beforeRAW and actual suffix/state audit produced; distinct postnative review still required. No source/Test/root/reader/contracts mutation after FINAL. Other own evidence/digest/PR plan may be created. Failed or partial execution must stop with retained evidence/versioned repair, no silent retry.

Create-only FINAL-review-v1.md/json with report/input_manifest absolute paths+SHA, RAWbefore/after,14personal pixel hashes, separate semantic/proof/canary/reader/registry/visual/scope/package verdicts and required_repairs. Requested Astra/medium; distinct reused staged automated actor/related history, not human/external/absolute-blind/runtime attestation. Bounded acceptance only. Native/postnative and concrete delivery pending. User already authorizes scoped commit/nonforcepush/draftPR; exact prospective PR plan stacks on stillOPENdraftunmerged PR212. Official attachment and actual delivery evidence required; no merge/deploy/retirement or Goal completion.
''')
capture('FINAL-stage-v1','git','add',*load(RUN/'candidate-stage-plan-v1.json')['stage'])
capture('FINAL-full-package-diff-v1','git','diff','--cached',BASE,'--check')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([PUBLIC,TEST,CONTRIBUTION,PDF,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',ROOT/'conversion-windows'/(TASK+'.md')])
paths.update(ROOT/d/(TASK+'.md') for d in ['proof-obligations','research-wiki/retrieval-index'])
paths.update(ROOT/p for p in ['lean-toolchain','lakefile.lean','lake-manifest.json','website/content/chapters.json','website/content/readings.json','website/content/highlights.json'])
paths.update(Path(r['path']) for r in load(RUN/'browser-generated-inputs-before-v1.json')['rows'])
fixed()
write(RUN/'FINAL-inputs-v1.json',dict(rows=rows(paths),source_commit=load(RUN/'registry-inspected-v1.json')['source_commit'],six_production_proofs=6,public_canaries=2,new_definitions=0,generated_Test_auxiliaries=0,source_container_closed=False,chapter_proof_total=None,chapter_complete=False,whole_Goal='ACTIVE'))
print('Exact FINAL packet prepared; distinct review pending.')
