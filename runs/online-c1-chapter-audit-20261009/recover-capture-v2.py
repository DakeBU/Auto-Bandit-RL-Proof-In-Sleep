from common_reader_v6 import *

fixed()
historical = load(RUN / 'formula-render-v1.json')
node = load(RUN / 'formula-render-v2-node-exit.json')
assert node['actual_exit'] == 0
assert sha(RUN / 'formula-render-v2-node.log') == node['log_sha256']
restored = []
# Preserve actual new output before repairing this task's accidental overwrite.
for suffix, key in [('browser.json', 'browser_report_sha256'), ('dom.html', 'DOM_sha256')]:
    old = RUN / ('formula-render-v1-' + suffix)
    new = RUN / ('formula-render-v2-' + suffix)
    current = old.read_bytes()
    write(new, current)
    rel = old.relative_to(ROOT).as_posix()
    blob = subprocess.check_output(['git', 'show', '78482effad9e21b00b54c3cc1db5e22f9737d729:' + rel])
    variants = [blob, blob.replace(b'\r\n', b'\n'), blob.replace(b'\r\n', b'\n').replace(b'\n', b'\r\n')]
    exact = [b for b in variants if hashlib.sha256(b).hexdigest() == historical[key]]
    assert exact, ('No byte-exact historical recovery', old)
    assert current != exact[0]
    old.write_bytes(exact[0])
    assert sha(old) == historical[key]
    restored.append(dict(path=old.as_posix(), restored_sha256=sha(old),
        preserved_actual_current_path=new.as_posix(), preserved_actual_current_sha256=sha(new)))
for row in historical['images']:
    assert sha(row['path']) == row['sha256']
r = load(RUN / 'formula-render-v2-browser.json')
assert r['url'] == node['command'][2]
assert r['profilePreserved'] == node['command'][4]
assert len(r['images']) == 10 and all('-v2.png' in p for p in r['images'])
assert len(r['panels']) == 5 and len(r['modulePanels']) == 4
assert not r['errors'] and not r['failed'] and not r['sourceHorizontalScrollers']
assert r['actualSourceGuideMathContainers'] == 24
assert all(p['mathContainers'] == 1 and p['mathErrors'] == 0 for p in r['panels'])
assert all(p['actualBuiltinWrapButtonClicked'] for p in r['modulePanels'])
reg = load(RUN / 'registry-v3.json')
assert reg['source_commit'] == '78482effad9e21b00b54c3cc1db5e22f9737d729'
for rel, digest in reg['module_HTML_sha256'].items():
    assert sha(SITE / rel) == digest
files = [SITE / 'chapters/online-foundations/index.html'] + [SITE / p for p in reg['module_HTML_sha256']]
write(RUN / 'capture-output-recovery-v2.json', dict(
    failure='capture-reader-v4.py exited 1 after actual Node exit 0: JS retained two v1 output names; expected v2 browser report absent',
    repair='Actual new bytes preserved under v2 names; original v1 bytes restored only after matching historical receipt SHA256 against committed Git bytes',
    restored=restored, historical_image_hashes_unchanged=True,
    actual_node_exit=0, failed_wrapper_exit=1, recovery_script_success_is_not_wrapper_success=True,
    source_commit=reg['source_commit'], production_and_Test_and_reader_unmodified=True))
write(RUN / 'formula-render-v2.json', dict(
    status='Actual Node capture 0; wrapper v4 postprocessing failed 1; versioned recovery validates current outputs; ROOT and distinct FINAL inspection pending',
    source_commit=reg['source_commit'], current_generated_HTML_sha256={p.as_posix():sha(p) for p in files},
    original_wrapper_executed_before_after_HTML_guard=True,
    retrospective_before_byte_snapshot_created=False,
    actual_command=node['command'], actual_node_exit=0, failed_wrapper_exit=1,
    DOM_sha256=sha(RUN / 'formula-render-v2-dom.html'),
    browser_report_sha256=sha(RUN / 'formula-render-v2-browser.json'),
    images=[dict(path=(RUN / p).as_posix(), sha256=sha(RUN / p)) for p in r['images']],
    task_owned_server_stopped_by_wrapper_finally=True, profile_preserved=r['profilePreserved'],
    source_guide_math_containers=24, chapter_complete=False, goal_complete=False))
write(RUN / 'capture-helper-failure-v4.md', '''The v4 Python wrapper failed with FileNotFoundError for formula-render-v2-browser.json AFTER the actual Node browser child exited 0 and after the wrapper's generated-HTML equality guard. A partial filename replacement in capture-reader-v2.cjs left two v1 output names. This accidentally overwrote this task's historical v1 browser report and DOM, not production, Tests, readers or generated site HTML.

Recovery preserved both new outputs byte-for-byte as v2, restored both historical v1 outputs only after matching their recorded SHA256 from committed Git bytes, and verified all ten historical image hashes unchanged. New outputs retain actual Node provenance, ten v2 images and source commit 78482effad9e21b00b54c3cc1db5e22f9737d729. No failed wrapper is reclassified as passed; recovery is a separately executed validation. The existing failed adapter and logs are retained. ROOT pixel review and distinct FINAL remain separate obligations.''')
fixed()
print('Historical bytes restored exactly; current actual Node outputs preserved and separately validated.')
