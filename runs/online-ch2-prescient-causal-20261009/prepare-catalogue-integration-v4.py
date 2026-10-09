from publication_guard_v2 import *
fixed()
s = (RUN / 'publication_guard_v2.py').read_text(encoding='utf8')
s = s.replace('online-ch2-prescient-causal-site-v2', 'online-ch2-prescient-causal-site-v3')
s = s.replace('render-repair-binding-v3.json', 'catalogue-repair-binding-v4.json')
s = s.replace("rp = RUN / 'render-repair-review-v3.json'", "rp = RUN / 'catalogue-repair-review-v4.json'")
s = s.replace("r['exact_math_delta_only']", "r['exact_boundary_delta_only']")
s = s.replace('exact-publication-plan-v3.json', 'exact-publication-plan-v4.json')
s = s.replace("'website/content/readings.json', 'website/content/highlights.json']", "'website/content/readings.json', 'website/content/highlights.json', 'website/content/declaration-boundaries.json']")
s = s.replace("    assert r['exact_boundary_delta_only']", "    assert r['exact_boundary_delta_only']\n    assert sha(RUN / 'render-repair-review-v3.json') == binding['prior_render_review_sha256']")
write(RUN / 'publication_guard_v3.py', s)
s = (RUN / 'prepare-stage-v2.py').read_text(encoding='utf8').replace('publication_guard_v2', 'publication_guard_v3')
s = s.replace("'website/content/readings.json', 'website/content/highlights.json',", "'website/content/readings.json', 'website/content/highlights.json', 'website/content/declaration-boundaries.json',")
s = s.replace('exact-publication-plan-v3.json', 'exact-publication-plan-v4.json')
for n in ['candidate-stage-plan', 'candidate-stage', 'candidate-full-diff-check', 'exact-RAW-line-ending-snapshots', 'candidate-diff-audit']:
    s = s.replace(n + '-v2', n + '-v3')
s = s.replace('only_five_old_paths_changed', 'only_six_old_paths_changed')
s = s.replace('full-harness-inspected-v1', 'full-harness-inspected-v2')
write(RUN / 'prepare-stage-v3.py', s)
s = (RUN / 'run-combined-gates-v1.py').read_text(encoding='utf8').replace('publication_guard_v1', 'publication_guard_v3')
for n in ['pre-harness-track-new-Lean', 'combined-root', 'combined-Tests', 'combined-root-Tests-inspected', 'combined-full-harness', 'full-harness-inspected']:
    s = s.replace(n + '-v1', n + '-v2')
write(RUN / 'run-combined-gates-v2.py', s)
s = (RUN / 'commit-and-build-site-v2.py').read_text(encoding='utf8').replace('publication_guard_v2', 'publication_guard_v3')
for n in ['candidate-stage-plan', 'candidate-diff-audit', 'candidate-commit', 'contributor-stack', 'contributor-main', 'site-build', 'site-check', 'registry-command', 'clean-candidate-site-binding']:
    s = s.replace(n + '-v2', n + '-v3')
s = s.replace('verify-registry-v2.py', 'verify-registry-v3.py').replace('full-harness-inspected-v1', 'full-harness-inspected-v2')
s = s.replace('Repair attainment-premise rendering with unchanged Lean contracts', 'Bound prescient iterate catalogue to its complete frozen definition')
write(RUN / 'commit-and-build-site-v3.py', s)
s = (RUN / 'verify-registry-v2.py').read_text(encoding='utf8').replace('publication_guard_v2', 'publication_guard_v3').replace('registry-inspected-v2', 'registry-inspected-v3')
write(RUN / 'verify-registry-v3.py', s)
s = (RUN / 'capture-prescient-reader-v3.cjs').read_text(encoding='utf8').replace('-v3.', '-v4.').replace('formula-render-v3-', 'formula-render-v4-')
definition = next(d for d in load(CONTRACT / 'stabilized-v1.json')['definitions'] if d['declaration'].endswith('.iterate'))['exact_definition']
expected = ' '.join(definition.split())
needle = "   if(code.scrollWidth>code.clientWidth+1)throw Error('Wrapped type clipped');"
assert s.count(needle) == 1
s = s.replace(needle, needle + "\n   if(node.id==='declaration:BanditRL.OnlinePrescientBregman.iterate' && code.text.replace(/\\s+/g,' ').trim()!==" + json.dumps(expected, ensure_ascii=False) + ")throw Error('Frozen complete iterate range differs or includes neighbor');")
write(RUN / 'capture-prescient-reader-v4.cjs', s)
s = (RUN / 'run-file-browser-capture-v3.py').read_text(encoding='utf8').replace('publication_guard_v2', 'publication_guard_v3')
for n in ['registry-inspected', 'clean-candidate-site-binding']:
    s = s.replace(n + '-v2', n + '-v3')
for n in ['browser-generated-inputs-before', 'browser-generated-inputs-after', 'reader-file-browser-capture-command', 'formula-render', 'online-ch2-prescient-causal-browser', 'capture-prescient-reader']:
    s = s.replace(n + '-v3', n + '-v4')
write(RUN / 'run-file-browser-capture-v4.py', s)
s = (RUN / 'prepare-FINAL-v4.py').read_text(encoding='utf8').replace('publication_guard_v2', 'publication_guard_v3')
for n in ['site-build', 'site-check', 'registry-command', 'contributor-stack', 'contributor-main', 'registry-inspected', 'clean-candidate-site-binding', 'candidate-stage-plan']:
    s = s.replace(n + '-v2', n + '-v3')
for n in ['formula-render', 'browser-generated-inputs-before', 'reader-file-browser-capture-command']:
    s = s.replace(n + '-v3', n + '-v4')
s = s.replace('SITEv2', 'SITEv3').replace('full-harness-inspected-v1', 'full-harness-inspected-v2')
s = s.replace("'render-repair-review-v3.json']:", "'render-repair-review-v3.json', 'catalogue-repair-review-v4.json']:")
s = s.replace('five-file', 'six-file').replace('five old paths', 'six old paths').replace('five-file/OWN', 'six-file/OWN')
s = s.replace('Personally inspect ALL22 originals', 'Catalogue repair also retained: root found iterate included the next theorem in SITEv2 despite registry/geometry passing. Exact plan-v4 appends one RAW/source-block-bound range to existing declaration-boundaries schema1, preserving old FTL entry and every old field. Generator/Lean unchanged; in-memory full scan exactly one statement delta and existing boundary tests passed. Current SITEv3 full combined rerun/registry/actual browser must verify exact frozen entire definition without neighbor.\n\nPersonally inspect ALL22 originals')
s = s.replace('10newnotes. Every old', '10newnotes; append exactly one frozen iterate range in declaration-boundaries.json, preserving old FTL entry. Every old')
s = s.replace('Original SITEv1 silent gathered alignment loss is preserved and not accepted.', 'Original SITEv1 silent gathered alignment loss and SITEv2 equation-definition neighboring theorem contamination are preserved and not accepted. Current iterate catalogue shows exactly its complete frozen definition, without the next theorem.')
s = s.replace('after root caught lost completion premise in SITEv1', 'after root caught lost completion premise in SITEv1 and neighboring-theorem contamination in SITEv2')
s = s.replace('Review eight exact', 'Review eight exact')
write(RUN / 'prepare-FINAL-v5.py', s)
write(RUN / 'catalogue-integration-helpers-v4.json', dict(all_create_only=True,
    canonical_config_not_materialized=True, prior_evidence_immutable=True,
    fresh_combined_gate_and_clean_SITEv3_required=True, stronger_actual_catalogue_assertion=True,
    whole_Goal_status='ACTIVE'))
fixed()
print('Prospective guarded six-path integration/combined/site/browser/FINAL helpers created only.')
