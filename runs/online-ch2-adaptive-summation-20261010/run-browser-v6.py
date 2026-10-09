from candidate_guard_v4 import *
candidate_fixed();actual_gates_fixed()
r=load(RUN/'registry-inspected-v1.json');assert r['lean_verified'] and r['new_production_nodes']==1
module=next(iter(r['module_HTML_sha256']))
inputs=[SITE/'chapters/online-ogd/index.html',SITE/'books/registry.json',SITE/'site-manifest.json',SITE/module]
before=rows(inputs)
assert subprocess.check_output(['git','show',r['source_commit']+':BanditRLProof/OnlineAdaptiveSummation.lean'])==MODULE.read_bytes()
node='C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe'
assert Path(node).is_file()
profile=ROOT/'tmp/online-ch2-adaptive-summation-browser-v2'
capture('browser-render-command-v3',node,RUN/'capture-integral-reader-v2.cjs',(SITE/'chapters/online-ogd/index.html').as_uri(),RUN,profile,SITE/'books/registry.json')
assert rows(inputs)==before
d=load(RUN/'formula-render-v2-browser.json');assert len(d['images'])==4 and not d['errors'] and not d['failed'] and not d['sourceHorizontalScrollers']
write(RUN/'browser-render-inspected-v2.json',dict(actual_exit=0,generated_inputs_before=before,generated_inputs_after=rows(inputs),generated_RAW_unchanged=True,original_PNGs=rows([RUN/p for p in d['images']]),personal_root_and_reviewer_pixel_inspection_pending=True,local_fileURI_desktop_only=True,deployed=False,chapter_complete=False,whole_Goal='active'))
candidate_fixed()
