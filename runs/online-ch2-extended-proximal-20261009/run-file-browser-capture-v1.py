from publication_guard_v1 import *
fixed()
receipt = load(RUN / 'registry-inspected-v1.json')
assert receipt['source_commit'] == load(RUN / 'clean-candidate-site-binding-v1.json')['actual_head']
registry = load(SITE / 'books/registry.json')
node = next(n for n in registry['nodes'] if n['id'] == 'declaration:BanditRL.OnlineBregman.proximal_one_step_extended')
inputs = [SITE / 'books/registry.json', SITE / 'chapters/online-ogd/index.html',
    SITE / node['url'].split('#')[0], SITE / 'site-manifest.json']
assert len(set(inputs)) == 4
write(RUN / 'browser-generated-inputs-before-v1.json', dict(rows=rows(inputs),
    scope='Four exact generated registry/chapter/new catalogue/manifest inputs.'))
profile = ROOT / 'tmp/online-ch2-extended-proximal-browser-v1/capture-profile'
assert not profile.exists()
capture('reader-file-browser-capture-command-v1',
    'C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe',
    RUN / 'capture-extended-reader-v1.cjs', (SITE / 'chapters/online-ogd/index.html').as_uri(), RUN, profile,
    SITE / 'books/registry.json', RUN / 'browser-production-nodes-v1.json', '9', '12')
b = load(RUN / 'formula-render-v1-browser.json')
assert len(b['images']) == 15 and len(b['panels']) == 11 and len(b['modulePanels']) == 3
assert not b['errors'] and not b['failed'] and b['actualSourceGuideMathContainers'] == 12 and not b['sourceHorizontalScrollers']
assert all(x['mathContainers'] == 1 and x['mathErrors'] == 0 and x['belowStickyNavigation'] for x in b['panels'])
assert all(x['actualBuiltinWrapButtonClicked'] and x['wrappedCode']['scrollWidth'] == x['wrappedCode']['clientWidth'] for x in b['modulePanels'])
for r in load(RUN / 'browser-generated-inputs-before-v1.json')['rows']:
    assert sha(r['path']) == r['sha256']
write(RUN / 'browser-generated-inputs-after-v1.json', dict(rows=rows(inputs), all_four_bytes_unchanged=True,
    scope='Four exact generated inputs only.', transport='Actual local file URI; no HTTP/live.'))
fixed()
print('Actual desktop DOM/MathJax/geometry/folded Lean/wrapped catalogue captured; fifteen originals require personal root and distinct FINAL inspection.')
