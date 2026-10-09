from integration_guard_v4 import *
fixed()
receipt=load(RUN/'registry-inspected-v1.json');registry=load(SITE/'books/registry.json')
assert receipt['source_commit']==load(RUN/'clean-candidate-site-binding-v1.json')['actual_head']
node=next(n for n in registry['nodes'] if n['id']=='declaration:BanditRL.OnlineFTLSelector.predict_prefix')
inputs=[SITE/'books/registry.json',SITE/'chapters/online-ogd/index.html',SITE/node['url'].split('#')[0],SITE/'site-manifest.json']
assert len(set(inputs))==4
write(RUN/'browser-generated-inputs-before-v1.json',dict(rows=rows(inputs),scope='Four exact generated registry/chapter/new catalogue/manifest inputs.'))
profile=ROOT/'tmp/online-ch2-reconciliation-browser-v1/capture-profile';assert not profile.exists()
capture('reader-file-browser-command-v1','C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe',RUN/'capture-ftl-reader-v1.cjs',(SITE/'chapters/online-ogd/index.html').as_uri(),RUN,profile,SITE/'books/registry.json',RUN/'browser-production-nodes-v1.json','14','17')
b=load(RUN/'formula-render-v1-browser.json')
assert len(b['images'])==28 and len(b['panels'])==14 and len(b['modulePanels'])==13
assert not b['errors'] and not b['failed'] and b['actualSourceGuideMathContainers']==17 and not b['sourceHorizontalScrollers']
assert all(x['mathContainers']==1 and x['mathErrors']==0 and x['belowStickyNavigation'] for x in b['panels'])
assert all(x['actualBuiltinWrapButtonClicked'] and x['wrappedCode']['scrollWidth']==x['wrappedCode']['clientWidth'] for x in b['modulePanels'])
for r in load(RUN/'browser-generated-inputs-before-v1.json')['rows']:assert sha(r['path'])==r['sha256']
write(RUN/'browser-generated-inputs-after-v1.json',dict(rows=rows(inputs),all_four_bytes_unchanged=True,transport='Actual local file URI; no HTTP/live.'))
fixed()
print('Actual desktop DOM/MathJax/wrap/fold captured;28originals await personal root and distinctFINAL review.',flush=True)
