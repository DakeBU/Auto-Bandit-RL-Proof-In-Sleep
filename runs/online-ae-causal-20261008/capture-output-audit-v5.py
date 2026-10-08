from common_reader_v4 import *
fixed_integrated()
receipt=load(RUN/'formula-render-v4-node-exit.json')
assert receipt['actual_exit']==0 and receipt['log_sha256']==sha(RUN/'formula-render-v4-node.log')
r=load(RUN/'formula-render-v1-browser.json')
assert len(r['panels'])==4 and len(r['modulePanels'])==3 and len(r['images'])==8
assert not r['errors'] and not r['failed'] and not r['sourceHorizontalScrollers']
assert all(p['mathContainers']==1 and p['mathErrors']==0 for p in r['panels'])
assert all(p['geometry']['scrollWidth']<=p['geometry']['clientWidth']+1 for p in r['panels']+r['modulePanels'])
assert all(p['actualBuiltinWrapButtonClicked'] for p in r['modulePanels'])
reg=load(RUN/'registry-v4.json');site=ROOT/'tmp/online-ae-causal-site-v4'
assert sha(site/'chapters/online-foundations/index.html')==reg['source_route_HTML_sha256']
assert all(sha(site/p)==h for p,h in reg['module_HTML_sha256'].items())
write(RUN/'capture-output-helper-repair-v5.json',dict(
    actual_Node_receipt='formula-render-v4-node-exit.json',actual_Node_exit=0,actual_captures=8,
    observed_outer_Python_v4_exit=1,outer_raw_stderr_saved=False,
    failure='Version-copy helper changed image suffixes but retained formula-render-v1-browser.json and formula-render-v1-dom.html output names; Python expected absent v4 filenames.',
    repair='Audit and bind the actual v4 browser execution outputs at their genuine names. Preserve all original files and helper versions; do not rerun or relabel screenshots.',
    images_all_genuine_v4=True,generated_HTML_unchanged_against_registry=True,
    not_an_exit_zero_only_rendering_claim=True,source_or_proof_changed=False))
write(RUN/'formula-render-v5.json',dict(status='8 actual original v4 images captured; ROOT/distinct FINAL inspection pending',
    actual_browser_execution_version=4,audit_version=5,source_commit=reg['source_commit'],
    actual_command=receipt['command'],Node_receipt_sha256=sha(RUN/'formula-render-v4-node-exit.json'),
    actual_DOM_file='formula-render-v1-dom.html',DOM_sha256=sha(RUN/'formula-render-v1-dom.html'),
    actual_browser_report_file='formula-render-v1-browser.json',browser_report_sha256=sha(RUN/'formula-render-v1-browser.json'),
    images=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in r['images']],
    task_owned_server_stopped=True,profile_preserved=r['profilePreserved'],generated_site_files_unmodified=True,
    source_guide_math_containers=r['actualSourceGuideMathContainers'],
    chapter_complete=False,goal_complete=False))
print('Audited genuine successful v4 browser outputs under retained original filenames; no capture rerun.',flush=True)
