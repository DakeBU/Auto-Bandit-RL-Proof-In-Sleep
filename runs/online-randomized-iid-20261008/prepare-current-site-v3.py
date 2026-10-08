from common_integrated_v2 import *

fixed_integrated()
assert load(RUN/'reader-context-repair-v3.json')['source_gate_applicable_by_unchanged_Lean_hashes']
prior=(RUN/'verify-registry-v2.py').read_text(encoding='utf8')
start=prior.index('for phrase in [');end=prior.index('module_path=',start)
phrases=['WHOLE infinite target process','strict-past','F_t contained in H_t','EVERY seed','a.s.',
    'outside expectation','SAME stream and prefix','XOR','two-round policy excess1/2',
    'Seven derived producer/interface proofs','not seven printed source results','asymptotic-success equivalence',
    'unknown(null)','five older main-relative','Goal remains ACTIVE','OPENdraft/unmerged PR194','Canonical main6847',
    'No real-valuedness, IID sequence, boundedness or horizon assumption','Only the seed codomain',
    'No feasibility, same-law or L2 assumption','still consumes a supplied information-restricted trace']
prior=prior[:start]+'for phrase in '+repr(phrases)+':\n    assert phrase in text,phrase\n'+prior[end:]
prior=prior.replace('online-randomized-iid-site-v2','online-randomized-iid-site-v3').replace("RUN/'registry-v2.json'","RUN/'registry-v3.json'")
write(RUN/'verify-registry-v3.py',prior)
s=(RUN/'capture-reader-v2.cjs').read_text(encoding='utf8')
for before,after in [('private-seed-source-card-v2','private-seed-source-card-v3'),('reader-first-viewport-v2','reader-first-viewport-v3'),
    ('public-note-${i+1}-v2','public-note-${i+1}-v3'),('module-new-declaration-${i+1}-v2','module-new-declaration-${i+1}-v3'),
    ('formula-render-v2','formula-render-v3')]:
    assert before in s,before
    s=s.replace(before,after)
write(RUN/'capture-reader-v3.cjs',s)
s=(RUN/'capture-reader-v2.py').read_text(encoding='utf8')
for before,after in [('online-randomized-iid-site-v2','online-randomized-iid-site-v3'),('registry-v2','registry-v3'),
    ('capture-reader-v2.cjs','capture-reader-v3.cjs'),('formula-render-v2','formula-render-v3')]:
    assert before in s,before
    s=s.replace(before,after)
write(RUN/'capture-reader-v3.py',s)
s=(RUN/'build-clean-site-v2.py').read_text(encoding='utf8')
for before,after in [('online-randomized-iid-site-v2','online-randomized-iid-site-v3'),
    ('online-randomized-iid-site-build-v2','online-randomized-iid-site-build-v3'),
    ('site-build-v2','site-build-v3'),('site-check-v2','site-check-v3'),('registry-check-v2','registry-check-v3'),
    ('verify-registry-v2.py','verify-registry-v3.py'),('current-reader-capture-v2','current-reader-capture-v3'),
    ('capture-reader-v2.py','capture-reader-v3.py')]:
    assert before in s,before
    s=s.replace(before,after)
s=s.replace("'Actual committed exact b08 stacked-base gate: five production paths/one own schema2 contract.'",
    "'Actual fresh contributor-current-reader-v3: five production paths/one own schema2 contract.'")
write(RUN/'build-clean-site-v3.py',s)
write(RUN/'obsolete-helper-guard-disclosure-v3.json',dict(
    helper='repair-contributor-output-parser-v3.py',
    issue='An unnecessary guessed full-hash equality in an OR with the actual known eight-character prefix was never true; the prefix branch passed.',
    actual_native_source_head='0b077dd58762bf13651a18880949821a725c0449',
    actual_integrated_gate_source_head_matches_full_git_oid=True,
    future_authority='The helper is historical only and must never run again. Future source/base guards use actual full Git OIDs and complete frozen proof/source bindings.',
    mathematical_or_NATIVE_gate_waiver=False,original_faulty_helper_retained=True,FINAL_must_assess=True))
print('Fresh v3 site/pixel/registry tools prepared; v2 bytes and current-reader repair preserved. Historical weak helper guard disclosed and superseded.')
