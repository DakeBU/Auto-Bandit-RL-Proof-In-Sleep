from publication_guard_v2 import *
fixed()
assert load(RUN/'registry-inspected-v1.json')['source_commit']=='3a81dd6ae283fce90b849d928c18094f37b6d3b7'
write(RUN/'preview-service-policy-rejection-v1.json',dict(action='Attempted Start-Process hidden Python HTTP preview listener on127.0.0.1:62430',outcome='exec_command rejected before execution',reported_reason='blocked by policy; no more specific reason returned',server_started=False,command_exit=None,service_retry=False,safer_alternative='Blocking actual browser visit to generated file URI; no preview HTTP listener started or alternative service launcher.',claim_boundary='File preview is local render only; it is not HTTP/deployment/live verification.',chapter_complete=False,whole_Goal_status='ACTIVE'))
registry=load(SITE/'books/registry.json')
node=next(n for n in registry['nodes'] if n['id']=='declaration:BanditRL.OnlineProximal.convex_minimizer_comparison')
inputs=[SITE/'books/registry.json',SITE/'chapters/online-ogd/index.html',SITE/node['url'].split('#')[0],SITE/'site-manifest.json']
assert len(set(inputs))==4
write(RUN/'browser-generated-inputs-before-v1.json',dict(rows=rows(inputs),scope='Four generated registry/chapter/catalogue/manifest inputs; not all site assets.'))
profile=ROOT/'tmp/online-ch2-proximal-browser-v1/capture-profile';assert not profile.exists()
capture('reader-file-browser-capture-command-v1','C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe',RUN/'capture-proximal-reader-v1.cjs',(SITE/'chapters/online-ogd/index.html').as_uri(),RUN,profile,SITE/'books/registry.json',CONTRACT/'stabilized-v1.json','7','10')
b=load(RUN/'formula-render-v1-browser.json')
assert len(b['images'])==4 and len(b['panels'])==2 and len(b['modulePanels'])==1
assert not b['errors'] and not b['failed'] and b['actualSourceGuideMathContainers']==10 and not b['sourceHorizontalScrollers']
assert all(x['mathContainers']==1 and x['mathErrors']==0 and x['belowStickyNavigation'] for x in b['panels'])
assert all(x['actualBuiltinWrapButtonClicked'] and x['wrappedCode']['scrollWidth']==x['wrappedCode']['clientWidth'] for x in b['modulePanels'])
for r in load(RUN/'browser-generated-inputs-before-v1.json')['rows']:assert sha(r['path'])==r['sha256']
write(RUN/'browser-generated-inputs-after-v1.json',dict(rows=rows(inputs),all_four_bytes_unchanged=True,scope='Four exact generated inputs only; no all-assets claim.',transport='actual local file URI, not HTTP/live'))
fixed();print('Actual local-file desktop DOM/MathJax/geometry/folded Lean/wrapped catalogue captured; four originals need personal root and distinct FINAL inspection.')
