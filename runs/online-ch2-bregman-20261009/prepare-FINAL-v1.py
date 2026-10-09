from publication_guard_v1 import *
fixed()
for label in ['site-build-v1','site-check-v1','registry-command-v1','reader-file-browser-capture-command-v1','contributor-stack-v1','contributor-main-v1']:
    assert load(RUN/(label+'.json'))['actual_exit']==0,label
reg=load(RUN/'registry-inspected-v1.json');browser=load(RUN/'formula-render-v1-browser.json')
assert reg['source_commit']=='69aeeeaf58364177a06bbc10329ea328c3c13b3c'
assert len(browser['images'])==14 and not browser['errors'] and not browser['failed']
assert browser['url'].startswith('file:///') and browser['actualSourceGuideMathContainers']==11
for row in load(RUN/'browser-generated-inputs-before-v1.json')['rows']:assert sha(row['path'])==row['sha256']
write(RUN/'root-reader-pixel-review-v1.json',dict(actor='/root',images=rows(RUN/n for n in browser['images']),image_count=14,tool='view_image detail original',source_commit=reg['source_commit'],observations='Personally inspected all14 originals: first viewport, source card, six teaching notes and six declaration catalogues. Ordered divergence and three-point signs, convexity/differentiability conditions and both negative proximal residuals match Lean. Distinguishes total default fderiv from source differentiability; initial point may lie outside V; actual minimum, nonsmooth loss, no sequence/existence claim. Full source and all8 Chapter2 forwards remain required/open. Exact Lean folded in notes; actual built-in catalogue wrapping fits long types. Dense desktop text readable, no visible clipping in these captures.',limits='Actual file URI1440px desktop only, not HTTP/deployment/live/mobile/all-viewports. No new HTTP preview service retried after prior rejection. Distinct FINAL must inspect these originals independently.',chapter_complete=False,whole_Goal_status='ACTIVE'))
retrieval=ROOT/'research-wiki/retrieval-index'/(TASK+'.md')
own=[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations']]
write(RUN/'pre-FINAL-own-metadata-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [CONTRIBUTION,retrieval,*own]]))
c=load(CONTRIBUTION)
c['verification']['bandit_check']='Actual combined root9109/Tests9278 cached-inclusive jobs and full tools/bandit.py check exit0,472tests/7existing skips, exporter/checkpassed. First current full attempt0; exact source bytes tracked beforehand. No test/rule/pin weakening.'
c['graph_contribution']['visual_review']='Actual selected8nodes (one definition/five proofs/two Tests),1619coalesced direct TYPE_VALUE presences/8required VALUE pairs and separately selected compiled numeric tails inspected. Complete shared registry10996unchanged records+6source-qualified production nodes. Actual local-file desktop DOM/strict geometry/14originals inspected by root; distinct FINAL pending.'
c['verification']['site_build']='Actual clean isolated SITEv1 build exit0 at69aeeeaf58364177a06bbc10329ea328c3c13b3c after applicable full combined Lean gate; no generated _site editing, later-head fresh build, deployment or live claim.'
c['verification']['site_check']='Actual SITEv1 check/registry exit0;10996complete prior records+6canonical production nodes, no Test/per-Book duplicates. Actual local-file browser11source-guide MathJax formulas/zeroerrors, strict desktop geometry, folded Lean/builtin catalogue wrap and14root-inspected originals;4exact generated input bytes unchanged. Distinct FINAL pending.'
c['verification']['independent_review']+=' Two nonempty contributor bases/site/registry and actual local-file DOM/original pixels passed; distinct bounded FINAL/native/delivery remain pending. No general source/chapter acceptance.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
suffix='\nIntegrated candidate: clean isolated site build/check/shared registry and two nonempty contributor bases passed at69aeeeaf58364177a06bbc10329ea328c3c13b3c. All10996 complete prior records preserved+6source-qualified production nodes. Local-file DOM11source-guide formulas/zeroerrors/strict desktop geometry/14originals inspected by root;4generated files unchanged. Not HTTP/live. General source/all8 Chapter2 forwards REQUIRED/OPEN; distinct FINAL/native/delivery pending; wholeGoalACTIVE.\n'
for p in [retrieval,*own]:p.write_bytes(p.read_bytes()+suffix.encode('utf8'))
write(RUN/'memory-digest-v3.md','# '+TASK+'\n\nCanonical definition plus5frozen Bregman proofs and2actual nonsmooth nonquadratic/boundary Test families. Actual minimum derives single-step comparison retaining both negative residuals; no assumed regret/stability bound. Generic public VALUEs/standard-only axioms,7native proof fences and definition guard; selected8nodes/1619direct TYPE_VALUE presences/8required VALUE pairs; both final numerical branches separately retain public proximal helper through Eq.mp. Root9109/Tests9278/full harness472tests7existing skips/exporter/checkpassed; first current full attempt0, source tracked beforehand. Two nonempty contributor bases and clean isolated SITEv1 build/check/registry at69aeeeaf58364177a06bbc10329ea328c3c13b3c;10996complete old records+6new production nodes. Actual local-file desktop11formula containers/zeroerrors/14root-inspected originals. Compiler/API/create-only-collision failures and two immutable SHA-bound received LaTex trailing-space exceptions retained: full diff2/scoped0 only those files. Canary raw-header and normalized-native hashes explicitly distinguished, no header change. Distinct FINAL/native/delivery pending; command runtime gates and file/semantic conventions separate. Full source EReal/local-extension/attainment/interiority/causal same-run fixed-variable telescopes REQUIRED/OPEN; all8forwards OPEN; chapter proof denominatornull; whole16GoalACTIVE.\n')
event('integrated-candidate-native-v1','candidate',dict(scope='Canonical definition/five Bregman dependency proofs/two Tests; full source OPEN',full_harness_sha256=sha(RUN/'full-harness-inspected-v1.json'),site_check_sha256=sha(RUN/'site-check-v1.json'),registry_sha256=sha(RUN/'registry-inspected-v1.json'),browser_sha256=sha(RUN/'formula-render-v1-browser.json'),root_pixels_sha256=sha(RUN/'root-reader-pixel-review-v1.json'),FINAL_pending=True,chapter_complete=False,goal_complete=False))
indices={sha(p):dict(path=p.as_posix(),encoding='raw-file') for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
def walk(obj,p,trail=''):
    if isinstance(obj,dict):
        for k,v in obj.items():
            if k in ['raw_base64','historical_raw_base64'] and isinstance(v,str):
                raw=base64.b64decode(v);indices[hashlib.sha256(raw).hexdigest()]=dict(path=p.as_posix(),encoding='embedded-exact-raw-base64',field=trail+'/'+k)
            else:walk(v,p,trail+'/'+k)
    elif isinstance(obj,list):
        for i,v in enumerate(obj):walk(v,p,trail+'/'+str(i))
for d in [RUN,CONTRACT]:
    for p in d.rglob('*.json'):walk(load(p),p)
resolutions=[]
for name in ['contract-review-v1.json','BODY-canary-contract-review-v1.json','canary-BODY-publication-review-v2.json','RAW-format-review-v1.json']:
    changes=[]
    for row in load(RUN/name)['raw_input_checks']:
        p=Path(row['path']);old=row.get('before_sha256') or row['sha256']
        if sha(p)!=old:
            assert old in indices,(name,p,old)
            changes.append(dict(path=p.as_posix(),historical_sha256=old,current_sha256=sha(p),exact_historical_snapshot=indices[old]))
    resolutions.append(dict(review=name,review_sha256=sha(RUN/name),changed_live_rows=changes,all_other_current_inputs_unchanged=True))
write(RUN/'FINAL-historical-binding-resolution-v1.json',dict(reviews=resolutions,scope='Actual approved staged transitions; historical reviews are not false current-live unchanged RAW claims.'))
stage=load(RUN/'candidate-stage-plan-v1.json')['stage'];capture('FINAL-stage-v1','git','add',*stage)
code,out=capture('FINAL-full-package-diff-v1','git','diff','--cached',BASE,'--check',required=False)
exceptions=load(RUN/'RAW-format-review-v1.json')['approved_RAW_exceptions'];expected={Path(x['path']).relative_to(ROOT).as_posix() for x in exceptions}
actual={line.split(':',1)[0] for line in out.splitlines() if ': trailing whitespace.' in line}
assert code==2 and actual==expected and ': new blank line at EOF.' not in out
for x in exceptions:assert sha(x['path'])==x['sha256']
capture('FINAL-scoped-package-diff-v1','git','diff','--cached',BASE,'--check','--','.',*[':(exclude)'+p for p in sorted(expected)])
write(RUN/'FINAL-diff-audit-v1.json',dict(actual_full_exit=2,exact_RAW_trailing_space_exceptions=exceptions,actual_scoped_exit=0,no_production_Test_reader_contract_exemptions=True,distinct_FINAL_adjudication_pending=True))
capture('FINAL-parent-PR208-v1','gh','pr','view','208','--json','number,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt,url')
write(RUN/'FINAL-packet-v1.md','''# Bounded Bregman foundation FINAL

Audit one canonical actual-fderiv definition, five frozen public proofs and two public nonsmooth Test families. Source Definition6.4/Lemma6.7 plus required Chapter2 prescient dependency. Algebraic self/three-point identities generalize source differentiability; default fderiv0 does not imply source validity. Convex nonnegativity requires both points in X and ambient derivative at base. Proximal result requires actual supplied minimum, real ConvexOn V loss, positive eta, ambient psi derivatives at BOTH old/new points; old point may lie outside V. No loss derivative or psi convexity/attainment theorem. BOTH negative residuals retained and cannot be dropped without separate nonnegativity. Complete inner-product space only gradient conversion. Retained old-base derivative hypothesis is source validity, unused in proof (compiler warning disclosed). No target weakening.

Not full Algorithm15.8/Theorem15.30, attained causal recursion or cumulative regret. Source X/interior and local-extension validity, EReal finite-domain/subgradient/convexity/minimum bridges, actual attained current-loss recursion/interior invariants and sharp fixed/variable same-run telescopes including main-text fixed-step exercise remain REQUIRED/OPEN. All8 Chapter2 forward containers open, chapter partial, proof denominatornull, whole16GoalACTIVE. No chapter6/15 acceptance.

Run publication_guard_v1.fixed; independently hash all FINAL inputs before/after. Prior contract/BODY/canary/reader/RAW reviews remain immutable, historical metadata changes resolved by exact embedded RAW snapshots. Check five production normalized statement hashes, two canary RAW-header versus normalized-native hash conventions and full canonical definition term. Inspect actual public VALUEs/14 standard-only axiom outputs and7safe native proof fences. Selected8nodes/1619coalesced direct TYPE_VALUE presences/8required VALUE pairs are not full transitive/source/registry count. Separately inspect compiled final numerical branches of BOTH Test conjunctions: Eq.mp with actual public helper, not only whole-conjunction edge. Nonquadratic divergences9/64 and11/64; nonsmooth minimum0 at center1/2. Boundary interval[0,1], old center-1 outsideV, actual minimum0, movement1/2. No claimed concrete Test VALUE use of nonnegativity (generic public VALUE is compiled).

Actual root9109/Tests9278/full harness472tests7existing skips/exporter/checkpassed first current full attempt; tracked source beforehand. No code/test/rule/toolchain weakening. Own shadow mismatches[]/would_mutatefalse/globalSGB unchanged. Two nonempty contributor bases. Clean isolated site source69aeeeaf58364177a06bbc10329ea328c3c13b3c sourceDirtyfalse: registry10996complete old records+6source-qualified production nodes, no Test/per-Book duplicates. No later-head fresh site claim.

Personally view ALL14 originals listed in formula-render-v1-browser.json with view_image original: viewport/source card/6notes/6catalogue declarations. Root pixels do not discharge yours. Actual local-file desktop,11source-guide MathJax formulas/zeroerrors, strict geometry/folded Lean/actual built-in catalogue wrapping;4exact generated input bytes unchanged. New HTTP preview service previously policy-rejected before execution, no retry/alternate service launcher. File render is not HTTP/live/mobile/all-viewports evidence. No generated _site edits.

Retain compiler/API/create-only-collision failures and normalized-vs-RAW hash distinction. Full package diff actual2 EXACTLY two SHA-bound immutable received decoder LaTex trailing spaces, scoped0 excludingONLYthose files. They are NOT EOF exceptions. No Lean/Test/reader/contract/source exemption. Preserve RAW/CRLF-to-LF differences exactly, no JSON reserialization/raw=Gitblob claim. Native CLI events, compiler, semantic and site gates separately evidenced, no single-runtime enforcement claim. Requested Astra/medium staged automated actors, reused related history, no human/external/absolute-blind/runtime attestation.

Create-only FINAL-review-v1.md/json with report/input hashes, independent RAW before/after, personal14pixel rows, separate semantic/proof/reader/registry/visual/scope/package verdicts, required_repairs, exact approved_RAW_exceptions and allowed OWN native/metadata closure. Bounded native counter5->0 proofs only; definition inventoried separately, not sixth proof/source denominator. Subsequent ordinary scoped commit/push/draftPR stacked on OPEN unmerged PR208 exact71f2219fa1648094eba8aa17b50e443258f436cb; native/postnative/actualdelivery separate. No merge/deploy/retirement/main/live/CI claim.
''')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([PUBLIC,CANARY,CONTRIBUTION,retrieval,PDF,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',*[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows']],*[ROOT/n for n in ['lean-toolchain','lakefile.lean','lake-manifest.json','website/scripts/build_site.py','website/scripts/check_site.py','tools/check_contributor_contract.py']],*[ROOT/'website/content'/n for n in ['chapters.json','readings.json','highlights.json']],*[Path(r['path']) for r in load(RUN/'browser-generated-inputs-before-v1.json')['rows']]])
fixed();write(RUN/'FINAL-inputs-v1.json',dict(rows=rows(paths),source_commit=reg['source_commit'],phase='Distinct bounded FINAL; native/delivery pending',production_proofs=5,canonical_definitions=1,public_canaries=2,new_registry_nodes=6,chapter_proof_total=None,chapter_complete=False,whole_Goal_status='ACTIVE'))
print('Bounded exact FINAL packet ready; distinct review pending.')
