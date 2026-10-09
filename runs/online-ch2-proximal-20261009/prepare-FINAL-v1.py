from publication_guard_v2 import *
fixed()
for label in ['site-build-v1','site-check-v1','registry-command-v1','reader-file-browser-capture-command-v1','contributor-stack-v1','contributor-main-v1']:
    assert load(RUN/(label+'.json'))['actual_exit']==0,label
reg=load(RUN/'registry-inspected-v1.json');browser=load(RUN/'formula-render-v1-browser.json')
assert reg['source_commit']=='3a81dd6ae283fce90b849d928c18094f37b6d3b7'
assert len(browser['images'])==4 and not browser['errors'] and not browser['failed']
assert browser['url'].startswith('file:///') and browser['actualSourceGuideMathContainers']==10
for row in load(RUN/'browser-generated-inputs-before-v1.json')['rows']:assert sha(row['path'])==row['sha256']
write(RUN/'root-reader-pixel-review-v1.json',dict(actor='/root',images=rows(RUN/n for n in browser['images']),image_count=4,tool='view_image detail original',source_commit=reg['source_commit'],observations='Personally inspected all four originals. First viewport distinguishes canonical local route compilation from cited textbook chapter completion. Derived source card and proof note show actual supplied minimum, arbitrary normed real E, nonsmooth convex f, only h derivative, the feasible segment and positive-tangent comparison, all-comparator quantification and required open general source. Formula signs match frozen Lean. Exact Lean remains folded in note; actual builtin wrap makes catalogue type fit. Dense desktop explanation is readable, no visible clipping in these captures.',limits='Actual local file URI at1440px desktop only, not HTTP/deployment/live/mobile/all-viewports. New preview HTTP service was policy-rejected; no alternative service launcher was tried. Distinct FINAL reviewer must inspect the same originals.',chapter_complete=False,whole_Goal_status='ACTIVE'))
retrieval=ROOT/'research-wiki/retrieval-index'/(TASK+'.md')
own=[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations']]
write(RUN/'pre-FINAL-own-metadata-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [CONTRIBUTION,retrieval,*own]]))
c=load(CONTRIBUTION)
c['graph_contribution']['visual_review']='Actual selected4nodes/1420coalesced direct TYPE_VALUE presences/6required VALUE pairs and separately selected compiled numeric tails inspected. Complete shared registry preserves10995 records+1source-qualified production node; no Test/per-Book duplicates. Actual local-file desktop DOM/strict geometry/4originals inspected by root; distinct FINAL pending.'
c['verification']['site_build']='Actual clean isolated SITEv1 build exit0 at3a81dd6ae283fce90b849d928c18094f37b6d3b7 with applicable unchanged Lean/root/pins full gate. No generated _site editing, fresh build at later evidence head, deployment or live claim.'
c['verification']['site_check']='Actual SITEv1 check/registry exit0;10995complete prior records+1canonical production proof. Actual local-file browser10source-guide MathJax formulas/zeroerrors, strict desktop geometry, folded Lean/builtin catalogue wrap and4originals personally inspected by root;4exact generated input bytes unchanged. HTTP preview service policy-rejected before execution; no service retry. Distinct FINAL pending.'
c['verification']['independent_review']+=' Current two nonempty contributor bases/site/registry and actual local-file DOM/original pixels passed. Distinct bounded FINAL/native/delivery remain pending; no general source or chapter acceptance.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
suffix='\nIntegrated candidate: actual clean isolated site build/check/shared registry and two nonempty contributor bases passed at3a81dd6ae283fce90b849d928c18094f37b6d3b7. All10995 complete old records preserved+1source-qualified production proof, no Test/per-Book duplication. Actual local-file DOM10source-guide formulas/zeroerrors/strict desktop geometry/4originals inspected by root. New HTTP preview service policy-rejected, no service retry; file rendering is not HTTP/live. General source/all8Chapter2forwards REQUIRED/OPEN; distinct FINAL/native/delivery pending, wholeGoalACTIVE.\n'
for p in [retrieval,*own]:p.write_bytes(p.read_bytes()+suffix.encode('utf8'))
write(RUN/'memory-digest-v3.md','# '+TASK+'\n\nOne frozen arbitrary real normed-space convex-minimizer comparison plus3nonsmooth/boundary/nonconvex-regularizer Test families. Actual supplied minimum, no assumed regret bound; no loss derivative or regularizer convexity. Actual focused/full public VALUE/standard axioms/4frozenheaders/6requiredcompiledVALUEpairs; two numeric tails directly retain helper after recorded B1 repair. Root9108/Tests9276/fullharness472tests7existing skips/exporter/checkpassed. Initial actual harness failure was untracked source inventory; exact2source tracking-only repair then full unchanged harness passed. Two nonempty contributor bases and clean SITEv1 build/check/registry at3a81dd6ae283fce90b849d928c18094f37b6d3b7 passed;10995complete old records+1newproof. Actual local-file desktop DOM10formula containers/zeroerrors/geometry/4root-inspected originals; no HTTP preview service started after policy rejection. Distinct FINAL/native/delivery pending. Historical compiler/API/native/representation/collision/B1/harness failures and exactly2SHA-bound immutable received decoder EOF exceptions retained. OWN native records are distinct from compiler/semantic/site gates, not one enforced runtime. Full general source/all8Chapter2forwards REQUIRED/OPEN, chapter proof denominatornull, whole16GoalACTIVE.\n')
event('integrated-candidate-native-v1','candidate',dict(scope='Only real nonsmooth minimizer comparison dependency and3Tests; general source OPEN',full_harness_sha256=sha(RUN/'full-harness-inspected-v1.json'),site_check_sha256=sha(RUN/'site-check-v1.json'),registry_sha256=sha(RUN/'registry-inspected-v1.json'),browser_sha256=sha(RUN/'formula-render-v1-browser.json'),root_pixels_sha256=sha(RUN/'root-reader-pixel-review-v1.json'),FINAL_pending=True,chapter_complete=False,goal_complete=False))
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
for name in ['contract-review-v1.json','BODY-canary-contract-review-v1.json','canary-BODY-review-v1.json','canary-BODY-publication-review-v2.json','publication-status-review-v2.json']:
    changes=[]
    for row in load(RUN/name)['raw_input_checks']:
        p=Path(row['path']);old=row.get('before_sha256') or row['sha256']
        if sha(p)!=old:
            assert old in indices,(name,p,old)
            changes.append(dict(path=p.as_posix(),historical_sha256=old,current_sha256=sha(p),exact_historical_snapshot=indices[old]))
    resolutions.append(dict(review=name,review_sha256=sha(RUN/name),changed_live_rows=changes,all_other_current_inputs_unchanged=True))
write(RUN/'FINAL-historical-binding-resolution-v1.json',dict(reviews=resolutions,scope='Actual approved staged transitions only; original reviews remain historical evidence, not current-live unchanged RAW claims.'))
stage=load(RUN/'candidate-stage-plan-v1.json')['stage'];capture('FINAL-stage-v1','git','add',*stage)
code,out=capture('FINAL-full-package-diff-v1','git','diff','--cached',BASE,'--check',required=False)
exceptions=load(RUN/'publication-status-review-v2.json')['approved_RAW_EOF_exceptions'];expected={Path(x['path']).relative_to(ROOT).as_posix() for x in exceptions}
actual={line.split(':',1)[0] for line in out.splitlines() if ': new blank line at EOF.' in line}
assert code==2 and actual==expected and ': trailing whitespace.' not in out
capture('FINAL-scoped-package-diff-v1','git','diff','--cached',BASE,'--check','--','.',*[':(exclude)'+p for p in sorted(expected)])
write(RUN/'FINAL-diff-audit-v1.json',dict(actual_full_exit=2,exact_RAW_EOF_exceptions=exceptions,actual_scoped_exit=0,no_production_Test_reader_contract_exemptions=True,distinct_FINAL_adjudication_pending=True))
capture('FINAL-parent-PR205-v1','gh','pr','view','205','--json','number,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt,url')
write(RUN/'FINAL-packet-v1.md','''# Bounded nonsmooth minimizer-comparison FINAL

Audit only one derived reusable real convex-minimizer comparison and three complementary Test families. Arbitrary real normed E generalizes finite-dimensional source; supplied actual minimum, no loss derivative/continuity, no h convexity, no V closed/open/bounded/coercive assumptions. Not full Algorithm15.8/Theorem15.30, an attained recursion or regret consumer. All eight Chapter2 forwards, Bregman/extended-real/subgradient bridges, actual attained current-loss recursion/interior validity and fixed/variable-step same-run terminals (including main-text proof left as exercise) remain REQUIRED/OPEN. Chapter proof denominatornull; whole16GoalACTIVE.

Run publication_guard_v2.fixed(); independently hash every FINAL RAW row before/after. Reuse immutable exact CONTRACT/BODY/canary/B1/reader/status reviews only through FINAL-historical-binding-resolution, not false live-byte assertions. Inspect actual public bodies,4frozen headers, full generic/public VALUE kernels and standard-only axioms. Selected graph4nodes/1420coalesced direct TYPE_VALUE presences/6required VALUE pairs is not full registry/source denominator. Separately inspect compiled numeric-tail audit: old NormNum head/helper absent vs current Eq.mp/helper present in BOTH final numerical branches, not only whole-conjunction edge.

Inspect root9108/Tests9276 and full harness472tests7existing skips/exporter/checkpassed; initial untracked allowlisted source inventory failure retained, exact2source staging-only repair, unchanged full harness then passed. No test skipping/rule/toolchain/math mutation. Own shadow mismatches[]/would_mutatefalse; global SGB untouched. Two nonempty contributor bases. Clean isolated site source3a81dd6ae283fce90b849d928c18094f37b6d3b7 build/check/shared registry all10995complete prior records+1source-qualified proof; no Test/per-Book duplicates, sourceDirtyfalse. No laterheadsitefresh claim.

Personally view ALL FOUR originals listed in formula-render-v1-browser.json with view_image original. Root inspection does not discharge yours. Actual local-file browser,10source-guide MathJax containers/zeroerrors, strict desktop geometry, folded exact Lean and actual builtin catalogue wrap. Full assumptions, feasible-segment proof, source-derived delta, actual mathlib facts and required open boundary visible. Four exact generated inputs unchanged. New hidden local HTTP preview service was automatic-policy-rejected before execution; no service retry/alternate launcher. Safer actual file-URI render succeeded without failed requests; this is not HTTP/deployment/live/all-viewports evidence. No generated _site edit.

Retain all actual compiler/API/representation/artifact-collision/B1/harness failures. Full package whitespace actualexit2 exactly two SHA-bound immutable received decoder EOF files; scopedexit0 excludes only them, no code/Test/reader/source/formula exemption. Preserve RAW/CRLF-to-LF differences exactly; no RAW=Gitblob claim. Functor audit none-found-with-reason, one setting only. Native CLI records, compiler, semantic and site gates are separate, not a single enforced runtime. Requested Astra/medium staged automated actors, no human/external/absolute-blind/runtime attestation.

Create-only FINAL-review-v1.md/json with report/input hashes and independent RAW before/after, personal4pixels, separate semantic/proof/reader/registry/visual/scope/package verdicts, required_repairs, exact whitespace exceptions and allowed OWN native/metadata closure scope. Bounded acceptance only:1->0 helper proof obligation, not chapter theorem count. Prospective ordinary scoped commit/push/draftPR stacked on OPEN unmerged PR205 exactbase29086b6f3a033f6536054f4d9a06ae0e9b2f8a91. No merge/deploy/retirement/main/live/CI claim. Native/post-native/actualdelivery separate.
''')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([PUBLIC,CANARY,CONTRIBUTION,retrieval,PDF,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',*[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows']],*[ROOT/n for n in ['lean-toolchain','lakefile.lean','lake-manifest.json','website/scripts/build_site.py','website/scripts/check_site.py','tools/check_contributor_contract.py']],*[ROOT/'website/content'/n for n in ['chapters.json','readings.json','highlights.json']],*[Path(r['path']) for r in load(RUN/'browser-generated-inputs-before-v1.json')['rows']]])
fixed();write(RUN/'FINAL-inputs-v1.json',dict(rows=rows(paths),source_commit=reg['source_commit'],phase='Distinct bounded package FINAL; native/delivery pending',production_proofs=1,public_canaries=3,new_registry_nodes=1,chapter_proof_total=None,chapter_complete=False,whole_Goal_status='ACTIVE'))
print('Bounded current FINAL exact packet ready; distinct review pending.')
