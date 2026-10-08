from common_reader_v3 import *
import functools, http.server, threading

fixed_integrated()
site = ROOT / 'tmp/online-completed-causal-site-v3'
reg = load(RUN / 'registry-v3.json')
files = [site / 'chapters/online-foundations/index.html'] + [
    site / p for p in reg['module_HTML_sha256']]
before = {p.as_posix(): sha(p) for p in files}
node = Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe')
profile = ROOT / 'tmp/online-completed-causal-playwright-v3-profile'
prior = load(ROOT / 'runs/online-ae-causal-20261008/formula-render-v1-browser.json')
assert not profile.exists()
with (RUN / 'formula-render-v3-server.log').open('x', encoding='utf8') as log:
    class Handler(http.server.SimpleHTTPRequestHandler):
        def log_message(self, fmt, *args):
            log.write((fmt % args) + '\n'); log.flush()
    server = http.server.ThreadingHTTPServer(('127.0.0.1', 0),
        functools.partial(Handler, directory=str(site)))
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start(); tick = time.monotonic()
    url = 'http://127.0.0.1:' + str(server.server_port) + '/chapters/online-foundations/index.html'
    command = [str(node), str(RUN / 'capture-reader-v3.cjs'), url, str(RUN),
        str(profile), str(site / 'books/registry.json'), str(CONTRACT / 'targets-v1.json'),
        str(reg['source_cards']), str(prior['actualSourceGuideMathContainers'] + 1)]
    try:
        child = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            creationflags=subprocess.CREATE_NO_WINDOW, timeout=55)
        write(RUN / 'formula-render-v3-node.log', child.stdout)
        write(RUN / 'formula-render-v3-node-exit.json', dict(command=command,
            actual_exit=child.returncode, seconds=time.monotonic()-tick,
            log_sha256=sha(RUN / 'formula-render-v3-node.log')))
        assert child.returncode == 0, child.stdout.decode('utf8', errors='replace')
    finally:
        server.shutdown(); server.server_close(); thread.join(timeout=2)
assert {p.as_posix(): sha(p) for p in files} == before
r = load(RUN / 'formula-render-v3-browser.json')
assert len(r['panels']) == 5 and len(r['modulePanels']) == 4 and len(r['images']) == 10
assert not r['errors'] and not r['failed'] and not r['sourceHorizontalScrollers']
assert all(p['mathContainers'] == 1 and p['mathErrors'] == 0 for p in r['panels'])
write(RUN / 'formula-render-v3.json', dict(
    status='10 actual original current images captured; formalizer/distinct FINAL inspections pending',
    source_commit=reg['source_commit'], generated_HTML_sha256=before, actual_command=command,
    DOM_sha256=sha(RUN / 'formula-render-v3-dom.html'),
    browser_report_sha256=sha(RUN / 'formula-render-v3-browser.json'),
    images=[dict(path=(RUN / p).as_posix(), sha256=sha(RUN / p)) for p in r['images']],
    task_owned_server_stopped=True, profile_preserved=profile.as_posix(),
    generated_site_files_unmodified=True, source_guide_math_containers=r['actualSourceGuideMathContainers'],
    chapter_complete=False, goal_complete=False))
fixed_integrated()
