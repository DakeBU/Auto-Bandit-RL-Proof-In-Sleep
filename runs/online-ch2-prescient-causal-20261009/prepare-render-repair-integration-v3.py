from publication_guard_v1 import *
fixed()
# Only create future guarded runners; this does not materialize the proposed repair.
s = (RUN / 'publication_guard_v1.py').read_text(encoding='utf8')
s = s.replace('online-ch2-prescient-causal-site-v1', 'online-ch2-prescient-causal-site-v2')
s = s.replace('publication-review-binding-v1.json', 'render-repair-binding-v3.json')
s = s.replace("rp = RUN / 'canary-BODY-publication-review-v1.json'", "rp = RUN / 'render-repair-review-v3.json'")
s = s.replace("    assert r['BODY_verdict'] in ['accepted', 'accepted-with-explicit-delta']\n", '')
s = s.replace('exact-publication-plan-v2.json', 'exact-publication-plan-v3.json')
s = s.replace("    assert sha(rp) == binding['review_sha256']", "    assert sha(rp) == binding['review_sha256']\n    assert sha(RUN / 'canary-BODY-publication-review-v1.json') == binding['original_canary_BODY_review_sha256']\n    assert r['exact_math_delta_only']")
write(RUN / 'publication_guard_v2.py', s)
s = (RUN / 'prepare-stage-v1.py').read_text(encoding='utf8')
s = s.replace('publication_guard_v1', 'publication_guard_v2').replace('exact-publication-plan-v2.json', 'exact-publication-plan-v3.json')
for name in ['candidate-stage-plan', 'candidate-stage', 'candidate-full-diff-check', 'exact-RAW-line-ending-snapshots', 'candidate-diff-audit']:
    s = s.replace(name + '-v1', name + '-v2')
write(RUN / 'prepare-stage-v2.py', s)
s = (RUN / 'commit-and-build-site-v1.py').read_text(encoding='utf8')
s = s.replace('publication_guard_v1', 'publication_guard_v2')
for name in ['candidate-stage-plan', 'candidate-diff-audit', 'candidate-commit', 'contributor-stack', 'contributor-main', 'site-build', 'site-check', 'registry-command', 'clean-candidate-site-binding']:
    s = s.replace(name + '-v1', name + '-v2')
s = s.replace('verify-registry-v1.py', 'verify-registry-v2.py')
s = s.replace('Prove current-loss partial Bregman recursion and transition bounds', 'Repair attainment-premise rendering with unchanged Lean contracts')
write(RUN / 'commit-and-build-site-v2.py', s)
s = (RUN / 'verify-registry-v1.py').read_text(encoding='utf8')
s = s.replace('publication_guard_v1', 'publication_guard_v2').replace('registry-inspected-v1', 'registry-inspected-v2')
write(RUN / 'verify-registry-v2.py', s)
s = (RUN / 'capture-prescient-reader-v1.cjs').read_text(encoding='utf8').replace('-v1.', '-v2.')
# Strengthen actual MathML checks: a container/error count does not ensure premise visibility.
needle = "   panels.push({selector,index,file,geometry,...math,actualViewport:page.viewportSize(),belowStickyNavigation:true});"
assert s.count(needle) == 1
s = s.replace(needle, "   if(file==='public-note-7-v2.png'){const mml=await panel.locator('mjx-assistive-mml').textContent();if(!mml.includes('\\u2200')||!mml.includes('argmin')||!mml.includes('\\u2203'))throw Error('Completion premise missing from actual MathML');}\n" + needle)
# Keep the Python helper itself ASCII; CJS receives exact UTF8 Unicode through escapes below.
write(RUN / 'capture-prescient-reader-v2.cjs', s)
s = (RUN / 'run-file-browser-capture-v1.py').read_text(encoding='utf8')
s = s.replace('publication_guard_v1', 'publication_guard_v2')
for name in ['registry-inspected', 'clean-candidate-site-binding', 'browser-generated-inputs-before', 'browser-generated-inputs-after', 'reader-file-browser-capture-command', 'formula-render', 'online-ch2-prescient-causal-browser', 'capture-prescient-reader']:
    s = s.replace(name + '-v1', name + '-v2')
write(RUN / 'run-file-browser-capture-v2.py', s)
s = (RUN / 'prepare-FINAL-v1.py').read_text(encoding='utf8')
s = s.replace('publication_guard_v1', 'publication_guard_v2')
for name in ['site-build', 'site-check', 'registry-command', 'reader-file-browser-capture-command', 'contributor-stack', 'contributor-main', 'registry-inspected', 'formula-render', 'clean-candidate-site-binding', 'browser-generated-inputs-before', 'candidate-stage-plan']:
    s = s.replace(name + '-v1', name + '-v2')
s = s.replace("    'canary-BODY-publication-review-v1.json']:", "    'canary-BODY-publication-review-v1.json', 'render-repair-review-v3.json']:")
s = s.replace("'canary-BODY-publication-review-v1.json']:", "'canary-BODY-publication-review-v1.json', 'render-repair-review-v3.json']:")
s = s.replace('Eight exact frozen derived production proofs', 'Eight exact frozen derived production proofs')
s = s.replace('Review eight exact frozen derived production proofs', 'Review repaired SITEv2 after root caught lost completion premise in SITEv1: gathered optional alignment consumed the bracket. Failure DOM/pixels retained; exact one-new-note math bigl/bigr repair distinctly reviewed, proof/contract/fullLean inputs unchanged. Review eight exact frozen derived production proofs')
s = s.replace('Clean isolated site source commit in binding', 'Clean isolated repaired SITEv2 source commit in binding')
write(RUN / 'prepare-FINAL-v2.py', s)
write(RUN / 'render-repair-integration-helpers-v3.json', dict(
    all_created_only=True, canonical_reader_not_yet_changed=True,
    second_site_clean_commit_required=True, original_failure_preserved=True,
    stronger_MathML_premise_assertion=True, whole_Goal_status='ACTIVE'))
fixed()
print('Prepared guarded v2 publication/site/browser/FINAL runners; exact repair review still required.')
