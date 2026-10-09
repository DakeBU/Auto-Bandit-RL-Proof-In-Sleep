from common_nonsmooth_publication_v5 import *
import base64

fixed()
for label in ['nonsmooth-site-build-v4','nonsmooth-site-check-v4','nonsmooth-registry-command-v2','nonsmooth-browser-node-v2']:
    assert load(RUN/(label+'.json'))['actual_exit']==0,label
reg=load(RUN/'nonsmooth-registry-inspected-v2.json')
browser=load(RUN/'nonsmooth-browser-capture-inspected-v1.json')
assert browser['source_commit']==reg['source_commit']
assert len(browser['images'])==8
for image in browser['images']:assert sha(image['path'])==image['sha256']
# Execute only AFTER /root has personally viewed all eight original current files.
write(RUN/'nonsmooth-root-pixel-review-v1.json',dict(actor='/root',
    personally_viewed_current_original_files=browser['images'],image_count=8,
    actual_view_tool='view_image detail original',source_commit=reg['source_commit'],
    observations='All8 original current images personally inspected. The source card renders the same three exact formulas in three readable rows; zero-normal qualification and Chapter2-incomplete boundary are visible. Three mathematical notes retain source/assumptions/proof/actual parents with initially folded exact Lean. Three catalogue declarations show complete types after the actual builtin wrap controls. No visible clipping or horizontal overflow in these1440px desktop captures.',
    scope='Current desktop only; no all-viewports or physical-device claim',
    actual_browser_report_sha256=sha(RUN/'formula-render-v1-browser.json'),distinct_FINAL_personal_pixels_pending=True,
    chapter_complete=False,whole_Goal_status='ACTIVE'))
write(RUN/'memory-digest-nonsmooth-current-candidate-v2.md',
    'Three actual frozen production proofs close TWO introductory nonsmooth source families; five meaningful complementary canary bodies. Distinct source/CONTRACT/BODY and neutral reconstruction retained, eight complete public VALUE kernels/standard-only axioms/eight native fences/13required actual VALUE pairs. Actual current root9106/Tests9272/fullharness472tests7skips/exporter/checkpassed applies to unchanged exact Lean/pins. Current clean isolated SITE4 build/check/registry passed; all10981 complete prior nodes unchanged plus3 public proof IDs, zero duplicate per-Book/Test nodes. Two nonempty contributor bases passed. Actual browser/DOM8images/8source-guide formulas/geometry passed; ROOT personally inspected8 current originals, distinct FINAL still required. Source inventory65 overlapping containers is enumeration only, proof denominatornull. Chapter2partial/Ch3-16unenumerated, eight required future references stay open; wholeGoalACTIVE. All actual proof/helper/contributor/reader/site/browser failures retained and typed. Native lifecycle/journal/own shadow are separate from math and semantic evidence, not one enforced runtime. No merge/deploy/main/live/CIpass/retirement claim.\n')
write(CONTRACT/'current-obligations-nonsmooth-candidate-v2.md',
    '# Current bounded nonsmooth candidate\n\nNS001–NS003: actual frozen production bodies, focused/public kernel/axioms and distinct BODY accepted; bounded package FINAL pending. C001–C005: operativev2 frozen contracts, complete public values, neutralv2 reconstruction and distinct BODY accepted. Exact original reader-v1 rejection and subsequent link/layout/formula display failures remain preserved; latest v5 display repair accepted and applied. Current root/Tests/fullharness, shadow, two nonempty contributor bases, clean local site/check/shared registry and strict browser geometry passed; ROOT8pixels inspected, distinct FINAL/native/delivery pending.\n\nSource enumerationv3 and new two-family binding are explicit; no Chapter2 acceptance is inferred. All32 numbered nonalgorithm containers,2algorithm boxes,18 overlapping groups,5additional audits and8forward/history containers require their own precise branch disposition; independent proof totalnull. Prescient observation and seven future mathematical references remain required/open; Ch7 history is navigation, while Ch7 maintext is required independently. Chapter1 delivered in unmerged PR203. Ch3–16 remain unenumerated. Whole16GoalACTIVE.\n')
event('nonsmooth-integration-repairs-native-v1','repair',dict(
    scope='Bounded nonsmooth publication integration; mathematical terminals unchanged',
    retained_failure_receipts=[sha(RUN/p) for p in ['nonsmooth-contributor-stack-v2.json','nonsmooth-site-build-v1.json','nonsmooth-site-check-v2.json','nonsmooth-browser-node-v1.json']],
    separately_accepted_reader_repairs=[sha(RUN/p) for p in ['nonsmooth-reader-repair-review-v2.json','nonsmooth-reader-link-repair-review-v3.json','nonsmooth-reader-layout-repair-review-v4.json','nonsmooth-formula-linebreak-review-v5.json']],
    no_statement_weakening=True,chapter_complete=False,goal_complete=False))
event('nonsmooth-integrated-candidate-native-v1','candidate',dict(
    scope='3 actual proofs/2 source families/5 canaries, not Chapter2 completion',
    full_harness=sha(RUN/'nonsmooth-full-harness-inspected-v1.json'),site_check=sha(RUN/'nonsmooth-site-check-v4.json'),
    registry=sha(RUN/'nonsmooth-registry-inspected-v2.json'),browser=sha(RUN/'nonsmooth-browser-capture-inspected-v1.json'),
    distinct_FINAL_pending=True,chapter_complete=False,goal_complete=False))
# Resolve previous stage bindings without pretending their old live paths stayed equal.
indices={sha(p):p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
prefixes={}
for path,suffix in [(ROOT/'BanditRLProof.lean',b'\nimport BanditRLProof.OnlineNonsmoothExamples\n'),(ROOT/'Tests.lean',b'\nimport Tests.OnlineNonsmoothExamplesCanary\n')]:
    raw=path.read_bytes();assert raw.endswith(suffix)
    before=raw[:-len(suffix)];h=hashlib.sha256(before).hexdigest()
    saved=RUN/('historical-prefix-'+path.name+'.json')
    write(saved,dict(current_path=path.as_posix(),actual_current_sha256=sha(path),exact_removed_suffix_base64=base64.b64encode(suffix).decode('ascii'),
        historical_raw_sha256=h,historical_raw_base64=base64.b64encode(before).decode('ascii')))
    prefixes[h]=saved
allowed={Path(r['path']).resolve() for r in load(CONTRACT/'nonsmooth-materialized-future-bytes-v1.json')['rows']}
resolved=[]
for name in ['source-contract-repair-review-v1.json','nonsmooth-production-BODY-review-v1.json','nonsmooth-canary-publication-review-v1.json',
    'nonsmooth-reader-repair-review-v2.json','nonsmooth-reader-link-repair-review-v3.json','nonsmooth-reader-layout-repair-review-v4.json','nonsmooth-formula-linebreak-review-v5.json']:
    review=load(RUN/name);changed=[]
    for row in review['raw_input_checks']:
        p=Path(row['path']);oldsha=row.get('before_sha256') or row['sha256']
        if sha(p)!=oldsha:
            assert p.resolve() in allowed,(name,p)
            snapshot=indices.get(oldsha) or prefixes.get(oldsha);assert snapshot,(name,p,oldsha)
            changed.append(dict(path=p.as_posix(),historical_sha256=oldsha,exact_historical_evidence=snapshot.as_posix(),current_sha256=sha(p),
                encoding='raw-file' if oldsha in indices else 'exact-prefix-bytes-base64'))
    resolved.append(dict(review=name,review_sha256=sha(RUN/name),changed_live_rows=changed,
        all_other_current_inputs_unchanged=True))
write(RUN/'nonsmooth-FINAL-historical-binding-resolution-v1.json',dict(reviews=resolved,
    rule='Only exact reviewed root/reader transitions; historical snapshots are not claimed current-live identical.',
    chapter_complete=False,whole_Goal_status='ACTIVE'))
capture('nonsmooth-FINAL-stage-v1','git','add',RUN.relative_to(ROOT).as_posix(),CONTRACT.relative_to(ROOT).as_posix())
code,out=capture('nonsmooth-FINAL-cumulative-full-diff-v1','git','diff','--cached',BASE,'--check',required=False)
exceptions=load(RUN/'nonsmooth-candidate-diff-audit-v1.json')['retained_exact_RAW_decoder_exceptions']
expected={Path(x['path']).relative_to(ROOT).as_posix():x['sha256'] for x in exceptions}
actual={s.split(':',1)[0] for s in out.splitlines() if ': trailing whitespace.' in s or ': new blank line at EOF.' in s}
assert code==2 and actual==set(expected)
for p,h in expected.items():assert sha(ROOT/p)==h
capture('nonsmooth-FINAL-cumulative-scoped-diff-v1','git','diff','--cached',BASE,'--check','--','.',*[':(exclude)'+p for p in sorted(actual)])
write(RUN/'nonsmooth-FINAL-cumulative-diff-audit-v1.json',dict(actual_full_exit=code,
    exact_RAW_exceptions=exceptions,exception_count=3,actual_scoped_exit=0,production_Test_reader_contract_exemptions=False,
    distinct_FINAL_adjudication_required=True))
capture('nonsmooth-FINAL-parent-PR203-v1','gh','pr','view','203','--json','number,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt,url')
write(RUN/'nonsmooth-FINAL-packet-v1.md', '''# Distinct bounded Chapter2 nonsmooth FINAL

Review this exact bounded package, not Chapter2/the whole book. Three actual new production proofs close TWO introductory families at printed16/PDF28; five actual complementary canaries. Operative source inventoryv3 is accepted as enumeration only,65 overlapping containers/null independent proof total; required forward references remain open. Do not promote this to chapter acceptance or main/live.

Independently hash every current RAW input before/after and rerun common_nonsmooth_publication_v5.fixed() to check the entire baseline plus only reviewed byte transitions. Reuse your prior source/CONTRACT/BODY review history only with exact matching fingerprints, disclose history. Personally view ALL8 current original screenshots from nonsmooth-browser-capture-inspected-v1.json with view_image; ROOT's inspection does not discharge yours. Assess source intent/seven slots, exact frozen3 production/operativev2 five canary types and actual bodies, complete8public VALUE kernels/standard-only axioms/eight native fences/13required compiled VALUE pairs, current combined root/Tests/fullharness markers, actual two-base nonempty contributor gates, clean SITE4/check/complete-old-registry preservation, actual DOM/8math/strict geometry and reader source/zero-normal qualification/all old notes retained.

Source qualification is separately reviewed, not author endorsement. All real labels/zero normal/zero dimension/ambient versus tangential at SAME point(1,3) remain explicit. C004v1 is retained as true but different-point diagnostic, v2 is operative. Source introduction is two families, not3numbered theorems. Current selected13nodes/1773coalesced TYPE_VALUE presences are not full graph or proof counts. Tests never become canonical production nodes. Three new nodes in one shared registry serve Books; all10981 full prior records/identity/links retained.

Failures and repairs must be adjudicated separately: actual missing import/scalar-inner compile failures; successful-kernel receipt parser/graph-output collision; reader-v1 absolute intuition rejection; precommit contributor N/A; wrong protected affected_files test metadata; unavailable generated auxiliary teaching-link; sixth-to-ninth note feature threshold; browser mistaken2-vs8 formula wait; actual overflow and single-field3-row display repair. Latest accepted v5 formula transform has exact inverse recovering all original formulas/punctuation, not changed mathematics. Actual canonical old root/reader bindings legitimately changed by approved versions; historical-binding-resolution gives exact evidence, no retroactive unchanged assertion. Cumulative diff has exactly3 frozen historical decoder RAW whitespace exceptions, no code/Test/reader/contract exemptions. Verify and decide these exceptions explicitly.

This is a distinct staged automated reviewer, requested Astra/medium, no runtime/human/external/absolute-blind attestation. Native log/journal/prompt conventions and Lean/semantic/site checks are separate, not one enforced runtime. Output create-only nonsmooth-FINAL-review-v1.md/json, bound current input_manifest/report and RAW checks; separate semantic/proof/reader/registry/visual/cumulative-scope/package verdicts, required_repairs and allowed metadata/native closure scope. PR/push/postnative delivery still pending; no merge/deploy authorized. Whole Goal ACTIVE, Chapter2 incomplete.\n''')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([PUBLIC,CANARY,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',CONTRIBUTION,
    ROOT/'research-wiki/retrieval-index/ONLINE-CH2-NONSMOOTH-20261009.md',PDF,
    ROOT/'website/content/chapters.json',ROOT/'website/content/readings.json',ROOT/'website/content/highlights.json',
    SITE/'chapters/online-subgradient-differentiability/index.html',SITE/'books/registry.json',SITE/'site-manifest.json',
    ROOT/'lean-toolchain',ROOT/'lakefile.lean',ROOT/'lake-manifest.json',ROOT/'website/scripts/build_site.py',ROOT/'website/scripts/check_site.py',ROOT/'tools/check_contributor_contract.py'])
paths.update(SITE/p for p in reg['module_HTML_sha256'])
for name in ['nonsmooth-production-BODY-review-input-v1.json','nonsmooth-canary-publication-review-input-v1.json']:
    paths.update(Path(x['path']) for x in load(RUN/name)['files'])
paths.update(ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows'])
assert all(p.is_file() for p in paths)
write(RUN/'nonsmooth-FINAL-inputs-v1.json',dict(rows=rows(paths),phase='distinct bounded package FINAL; native/delivery pending',
    source_commit=reg['source_commit'],new_public_proofs=3,new_source_families=2,canaries=5,chapter_proof_total=None,
    chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Bounded FINAL current RAW packet ready; independent personal pixels and package decision remain required.')
