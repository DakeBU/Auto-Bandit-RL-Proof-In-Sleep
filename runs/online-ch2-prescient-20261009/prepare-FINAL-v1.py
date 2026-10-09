from publication_guard_v3 import *
import copy

fixed()
for label in ['site-build-v2','site-check-v2','registry-command-v2','reader-browser-capture-command-v1','contributor-stack-v2','contributor-main-v2']:
    assert load(RUN/(label+'.json'))['actual_exit']==0,label
reg=load(RUN/'registry-inspected-v1.json')
browser=load(RUN/'formula-render-v1-browser.json')
assert reg['source_commit']=='5680bcca81c5f894b801c0599689f2a5870e8306'
assert len(browser['images'])==16 and not browser['errors'] and not browser['failed']
assert len(browser['panels'])==8 and len(browser['modulePanels'])==7
assert browser['actualSourceGuideMathContainers']==9 and not browser['sourceHorizontalScrollers']
assert all(x['mathContainers']==1 and x['mathErrors']==0 and x['belowStickyNavigation'] for x in browser['panels'])
assert all(x['actualBuiltinWrapButtonClicked'] and x['wrappedCode']['scrollWidth']==x['wrappedCode']['clientWidth'] for x in browser['modulePanels'])
before=load(RUN/'browser-generated-inputs-before-v1.json')['rows']
assert len(before)==4
for row in before:assert sha(row['path'])==row['sha256']
write(RUN/'browser-generated-inputs-after-v1.json',dict(rows=rows(Path(r['path']) for r in before),all_four_bytes_unchanged=True,scope='Four exact generated registry/chapter/catalogue/manifest inputs only; not all assets.'))
write(RUN/'root-reader-pixel-review-v1.json',dict(actor='/root',images=rows(RUN/n for n in browser['images']),image_count=16,
    tool='view_image detail original',source_commit=reg['source_commit'],
    observations='Personally inspected all sixteen originals: first viewport distinguishes local route compilation from source chapter completion; source card and seven notes expose current-before-prediction timing, actual movement and terminal residuals, initial ambient center, complete-Hilbert extension and required open general source. Seven catalogue statements fit after actual builtin wrap controls. Formula renderings and signs agree with frozen Lean; exact Lean remains initially folded in notes. No visible clipping in these desktop captures.',
    limits='Actual 1440px desktop only, no mobile/all-viewports or physical-device claim; distinct FINAL reviewer must inspect originals independently.',chapter_complete=False,whole_Goal_status='ACTIVE'))

manifest=ROOT/'research-wiki/contribution-contracts'/(TASK+'.json')
retrieval=ROOT/'research-wiki/retrieval-index'/(TASK+'.md')
own=[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations']]
write(RUN/'pre-FINAL-own-metadata-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [manifest,retrieval,*own]]))
c=load(manifest)
c['graph_contribution']['visual_review']='Actual compiled selected graph29nodes/3538coalesced TYPE_VALUE presences/12required VALUE pairs inspected. Complete shared registry preserves10984 prior records plus11 source-qualified production nodes (7proofs/4definitions), no per-Book/Test duplication. Actual desktop DOM/strict geometry/16originals inspected by root; distinct FINAL pixels pending.'
c['verification']['site_build']='Actual clean isolated SITEv2 build exit0 at5680bcca81c5f894b801c0599689f2a5870e8306; exact unchanged Lean/root/pins full gate applies. First actual site failure retained and separately reviewed link repair applied. No generated _site editing or deployment.'
c['verification']['site_check']='Actual SITEv2 check/registry exit0;10984 complete prior nodes plus11 new shared production nodes. Actual browser9source-guide MathJax containers/zeroerrors, strict desktop geometry and16originals inspected by root. Four exact generated inputs unchanged through browser capture; distinct FINAL pending.'
c['verification']['independent_review']+=' Current repaired site/check/registry, two nonempty contributor bases and actual DOM/original pixels passed. Distinct bounded FINAL/native/delivery still pending; no chapter acceptance.'
manifest.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
suffix='\nCurrent candidate update: actual clean SITEv2 build/check/shared registry and two nonempty contributor bases passed. All10984 complete prior nodes preserved plus11 source-qualified production nodes(7proofs/4definitions); no Test or per-Book duplicates. Actual9 source-guide MathJax formulas/zeroerrors, desktop geometry and16original screenshots inspected by root. Three actual nondegenerate public API instances also compile with standard-only axioms. Historical sitev1 link failure and exact6note repair retained. FINAL/native/delivery pending. Historical pending statements above describe their own stages. General source and all8Chapter2forward containers REQUIRED/OPEN; whole Goal ACTIVE.\n'
retrieval.write_bytes(retrieval.read_bytes()+suffix.encode('utf8'))
for p in own:p.write_bytes(p.read_bytes()+suffix.encode('utf8'))
write(RUN/'memory-digest-v3.md','# '+TASK+'\n\nSeven frozen actual affine prescient production proofs and five complementary public canaries, three extra nondegenerate production API values, all standard-only axioms and unchanged frozen headers. Same-run projection/minimizer/current-inclusive prefix/telescope producer chain, no assumed stability oracle. Current root9107/Tests9274 cached-inclusive jobs and fullharness472tests/7existing skips/exporter/checkpassed. Current clean SITEv2/check/shared registry and two nonempty contributor bases passed;10984 complete old records+11 production nodes. Actual9source-guide formulas/zeroerrors/strict desktop geometry/16root-inspected originals. Distinct FINAL/native/delivery pending. General convex/Bregman/variable-step source and all8Chapter2forward containers REQUIRED/OPEN; proof denominatornull; whole16GoalACTIVE. Historical failures,2exact immutable decoder EOF exceptions and durable RAW/CRLF snapshots preserved. OWN native records are distinct from compiler/semantic/site evidence, not a single enforced runtime. No merge/deploy/main/live/retirement.\n')
event('publication-repair-native-v1','repair',dict(scope='Reader integration only; twelve frozen proof/canary terminals unchanged',actual_site_failure_sha256=sha(RUN/'site-build-v1.json'),separate_repair_review_sha256=sha(RUN/'reader-link-repair-review-v3.json'),current_site_actual_exit=0,no_mathematical_weakening=True,chapter_complete=False,goal_complete=False))
event('integrated-candidate-native-v1','candidate',dict(scope='Bounded affine prescient foundation only, general source OPEN',full_harness_sha256=sha(RUN/'full-harness-inspected-v1.json'),site_check_sha256=sha(RUN/'site-check-v2.json'),registry_sha256=sha(RUN/'registry-inspected-v1.json'),browser_sha256=sha(RUN/'formula-render-v1-browser.json'),root_pixels_sha256=sha(RUN/'root-reader-pixel-review-v1.json'),FINAL_pending=True,chapter_complete=False,goal_complete=False))

# Resolve historical live bindings against exact RAW snapshots; never assert they stayed current.
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
    for p in d.rglob('*.json'):
        walk(load(p),p)
resolutions=[]
for name in ['complete-production-BODY-review-v1.json','canary-BODY-publication-review-v1.json','reader-status-and-RAW-review-v2.json','reader-link-repair-review-v3.json']:
    changes=[]
    for row in load(RUN/name)['raw_input_checks']:
        p=Path(row['path']);old=row.get('before_sha256') or row['sha256']
        if sha(p)!=old:
            assert old in indices,(name,p,old)
            changes.append(dict(path=p.as_posix(),historical_sha256=old,current_sha256=sha(p),exact_historical_snapshot=indices[old]))
    resolutions.append(dict(review=name,review_sha256=sha(RUN/name),changed_live_rows=changes,all_other_current_inputs_unchanged=True))
write(RUN/'FINAL-historical-binding-resolution-v1.json',dict(reviews=resolutions,scope='Actual approved staged transitions only; original reviews remain historical evidence, not a claim of current-live unchanged RAW.'))
stage=load(RUN/'candidate-stage-plan-v1.json')['stage']
capture('FINAL-stage-v1','git','add',*stage)
code,out=capture('FINAL-full-package-diff-v1','git','diff','--cached',BASE,'--check',required=False)
exceptions=load(RUN/'reader-status-and-RAW-review-v2.json')['approved_RAW_EOF_exceptions']
expected={Path(x['path']).relative_to(ROOT).as_posix() for x in exceptions}
actual={line.split(':',1)[0] for line in out.splitlines() if ': new blank line at EOF.' in line}
assert code==2 and actual==expected and ': trailing whitespace.' not in out
capture('FINAL-scoped-package-diff-v1','git','diff','--cached',BASE,'--check','--','.',*[':(exclude)'+p for p in sorted(expected)])
write(RUN/'FINAL-diff-audit-v1.json',dict(actual_full_exit=2,exact_RAW_EOF_exceptions=exceptions,actual_scoped_exit=0,no_production_Test_reader_contract_exemptions=True,distinct_FINAL_adjudication_pending=True))
capture('FINAL-parent-PR204-v1','gh','pr','view','204','--json','number,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt,url')
write(RUN/'FINAL-packet-v1.md','''# Bounded affine prescient FINAL

Independently audit this exact package, not Chapter2 or Theorem15.30. Seven frozen production proofs form one affine/quadratic Euclidean prescient dependency chain, extended explicitly to complete real Hilbert spaces. Five complementary public canaries and three extra nondegenerate production API VALUE instances. Full general convex/subdifferentiable/Bregman/variable-step source container, including constant-step source proof left as exercise, and all eight required Chapter2 forward containers stay REQUIRED/OPEN. Whole16GoalACTIVE.

Run publication_guard_v3.fixed() and independently hash every manifest RAW input before/after. Reuse exact earlier CONTRACT/BODY reviews only with their immutable hashes and FINAL-historical-binding-resolution; old mutable live rows are not claimed unchanged. Inspect actual public bodies, twelve frozen headers, actual full public VALUE kernels/standard-only axioms/native checks and29node/3538coalesced direct TYPE_VALUE selected graph with12required VALUE pairs. Selected graph counts are not full registry/source-result denominators. Review NondegeneratePublicAPIProbe.lean and actual receipt: sharp -7/2, source -13/4 and real proximal minimizer with offset3 at actual active constrained trajectory. These are used theorem values, not unused premises.

Assess actual root9107/Tests9274/fullharness472tests7existing skips/exporter/checkpassed, two nonempty contributor bases, clean SITEv2 source5680bcca81c5f894b801c0599689f2a5870e8306 build/check, complete10984 old node preservation+11 source-qualified production nodes. No Test/per-Book duplication. Personally inspect ALL16 current original images listed in formula-render-v1-browser.json using view_image original; root review does not discharge yours. Actual9source-guide MathJax formulas, strict desktop geometry, builtin catalogue wrapping, current-before-prediction information, actual negative movement/terminal terms, arbitrary ambient initial center, allT including0, folded exact Lean, source/assumption/proof/parents/open boundary must match. Four generated input bytes remain unchanged through capture. No all-viewports claim.

Adjudicate retained compiler/API/representation/native-header/metadata-helper/site failures and exact separately reviewed reader repairs. Sitev1 actual failed because three genuine compiled constants lacked standalone registry anchors; six new notes remove only unavailable link entries and retain constant names/explanation/full compiled graph. Full package whitespace actualexit2 is EXACTLY two SHA-bound immutable received decoder EOF reports; scopedexit0 excludes only those, no code/Test/reader/contract exceptions. Preserve reviewed RAW versus Git CRLF-to-LF differences with durable exact snapshots; no claim Git blobs equal RAW. Native record/journal, Lean, semantic and site gates are distinct, not one enforced runtime.

Create-only FINAL-review-v1.md/json: bind report/input hashes and independent RAW before/after checks, personal16pixels, separate semantic/proof/reader/registry/visual/scope/package verdicts, required repairs, and precise allowed OWN metadata/native closure scope. Bounded package acceptance only; native/delivery pending. Requested Astra/medium staged automated actors, no human/external/absolute-blind/runtime attestation. No merge/deployment/main/live/retirement.
''')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([PUBLIC,CANARY,manifest,retrieval,PDF,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',*[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows']],*[ROOT/n for n in ['lean-toolchain','lakefile.lean','lake-manifest.json','website/scripts/build_site.py','website/scripts/check_site.py','tools/check_contributor_contract.py']],*[ROOT/'website/content'/n for n in ['chapters.json','readings.json','highlights.json']],*[Path(r['path']) for r in before]])
fixed()
write(RUN/'FINAL-inputs-v1.json',dict(rows=rows(paths),source_commit=reg['source_commit'],phase='distinct bounded package FINAL; native/delivery pending',production_proofs=7,public_canaries=5,new_registry_nodes=11,chapter_proof_total=None,chapter_complete=False,whole_Goal_status='ACTIVE'))
print('Bounded FINAL exact current packet ready; distinct review remains pending.')
