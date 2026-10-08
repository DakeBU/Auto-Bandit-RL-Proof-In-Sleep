from common_reader_v3 import *

fixed_integrated()
receipt = load(RUN / 'formula-render-v3-node-exit.json')
assert receipt['actual_exit'] == 0
assert receipt['log_sha256'] == sha(RUN / 'formula-render-v3-node.log')
r = load(RUN / 'formula-render-v1-browser.json')
assert len(r['panels']) == 5 and len(r['modulePanels']) == 4 and len(r['images']) == 10
assert all(x.endswith('-v3.png') for x in r['images'])
assert not r['errors'] and not r['failed'] and not r['sourceHorizontalScrollers']
assert all(p['mathContainers'] == 1 and p['mathErrors'] == 0 for p in r['panels'])
assert all(p['geometry']['scrollWidth'] <= p['geometry']['clientWidth'] + 1
           for p in r['panels'] + r['modulePanels'])
assert all(p['geometry']['left'] >= 0 and p['geometry']['right'] <= 1441
           for p in r['panels'] + r['modulePanels'])
assert all(p['actualBuiltinWrapButtonClicked'] for p in r['modulePanels'])
reg = load(RUN / 'registry-v3.json'); site = ROOT / 'tmp/online-completed-causal-site-v3'
assert sha(site / 'chapters/online-foundations/index.html') == reg['source_route_HTML_sha256']
assert all(sha(site / p) == h for p, h in reg['module_HTML_sha256'].items())
write(RUN / 'capture-output-reader-repair-v4.json', dict(
    actual_successful_Node_receipt='formula-render-v3-node-exit.json', actual_Node_exit=0,
    actual_captures=10, observed_outer_Python_v3_exit=1, outer_raw_stderr_saved=False,
    failure='Version copying changed image suffixes but only replaced -v1. and -v1.png, omitting -v1- in browser/DOM names. Python expected nonexistent v3 browser file.',
    repair='Bind actual successful v3 browser execution outputs at genuine retained v1 names, without rerendering/renaming images or editing generated HTML.',
    images_all_genuine_v3=True, previous_v1_v2_overflow_failures_retained=True,
    no_new_capture_or_compilation_claim=True))
write(RUN / 'formula-render-v4.json', dict(
    status='10 genuine original v3 images; formalizer/distinct FINAL pixel inspections pending',
    actual_browser_execution_version=3, audit_version=4, source_commit=reg['source_commit'],
    actual_command=receipt['command'], Node_receipt_sha256=sha(RUN / 'formula-render-v3-node-exit.json'),
    actual_DOM_file='formula-render-v1-dom.html', DOM_sha256=sha(RUN / 'formula-render-v1-dom.html'),
    actual_browser_report_file='formula-render-v1-browser.json',
    browser_report_sha256=sha(RUN / 'formula-render-v1-browser.json'),
    images=[dict(path=(RUN / p).as_posix(), sha256=sha(RUN / p)) for p in r['images']],
    task_owned_server_stopped=True, profile_preserved=r['profilePreserved'],
    generated_site_files_unmodified=True, source_guide_math_containers=r['actualSourceGuideMathContainers'],
    chapter_complete=False, goal_complete=False))
source = (RUN / 'prepare-FINAL-review-v3.py').read_text(encoding='utf8')
source = source.replace('pixel-review-v3.json', 'pixel-review-v4.json')
source = source.replace('formula-render-v3.json', 'formula-render-v4.json')
source = source.replace('actual browser math/geometry/wrap checks',
    'actual v3 browser math/geometry/wrap checks, genuine v1-named browser/DOM outputs, failed Python-v3 filename lookup and exact audit-v4 binding without rerender/rename')
source = source.replace('Actual Lean/type-printer/receipt-reader failures',
    'Actual Lean/type-printer/receipt-reader/capture-output filename failures')
write(RUN / 'prepare-FINAL-review-v4.py', source)
source = (RUN / 'common_accepted_v3.py').read_text(encoding='utf8')
write(RUN / 'common_accepted_v4.py', source.replace('formula-render-v3.json', 'formula-render-v4.json'))
for filename in ['record-acceptance-v3.py', 'prepare-post-native-review-v3.py',
                 'prepare-reviewed-commit-v3.py', 'deliver-reviewed-draft-v3.py']:
    source = (RUN / filename).read_text(encoding='utf8')
    source = source.replace('common_accepted_v3', 'common_accepted_v4')
    source = source.replace('genuine v3 browser/DOM/capture evidence; actual v1/v2 overflow and v3 diagnostic retained',
        'actual v3 capture/v1-named browser outputs bound by audit-v4; two overflow failures/diagnostic/filename failure retained')
    write(RUN / filename.replace('-v3.py', '-v4.py'), source)
print('Actual Node v3 geometry/math/wrap passed;10 original captures bound at genuine filenames. Pixel inspections/FINAL pending.', flush=True)
