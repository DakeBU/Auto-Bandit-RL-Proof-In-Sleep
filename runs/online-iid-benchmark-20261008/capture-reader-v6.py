from common_integrated_v2 import *
import functools, http.server, threading

fixed_integrated()
site = ROOT / 'tmp/online-iid-benchmark-site-v6'
page = site / 'chapters/online-foundations/index.html'
module = site / load(RUN / 'registry-v6.json')['module_path']
before = [sha(page), sha(module)]
exe = Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe')
profile = ROOT / 'tmp/online-iid-benchmark-playwright-v1-profile'
with (RUN / 'formula-render-v6-server.log').open('w', encoding='utf8') as log:
    class Handler(http.server.SimpleHTTPRequestHandler):
        def log_message(self, fmt, *args): log.write((fmt % args) + '\n'); log.flush()
    server = http.server.ThreadingHTTPServer(('127.0.0.1', 0), functools.partial(Handler, directory=str(site)))
    thread = threading.Thread(target=server.serve_forever, daemon=True); thread.start(); tick=time.monotonic()
    url = 'http://127.0.0.1:' + str(server.server_port) + '/chapters/online-foundations/index.html'
    command = [str(exe), str(RUN / 'capture-reader-v6.cjs'), url, str(RUN), str(profile), str(site / 'books/registry.json')]
    try:
        child = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, creationflags=subprocess.CREATE_NO_WINDOW, timeout=55)
        write(RUN / 'formula-render-v6-node.log', child.stdout)
        assert child.returncode == 0, child.stdout.decode('utf8', errors='replace')
    finally:
        server.shutdown(); server.server_close(); thread.join(timeout=2)
assert [sha(page), sha(module)] == before
r = load(RUN / 'formula-render-v6-browser.json')
assert len(r['panels']) == 9 and len(r['modulePanels']) == 4 and len(r['images']) == 14
assert all(x['mathErrors'] == 0 for x in r['panels']) and not r['sourceHorizontalScrollers']
write(RUN / 'formula-render-v6.json', dict(status='Actual14current panels captured; ROOT pixel review pending',
    generated_page_sha256=before[0], module_page_sha256=before[1], site_source_commit=load(RUN / 'registry-v6.json')['source_commit'],
    actual_command=command, elapsed_seconds=time.monotonic()-tick, DOM_sha256=sha(RUN / 'formula-render-v6-dom.html'),
    browser_report_sha256=sha(RUN / 'formula-render-v6-browser.json'),
    images=[dict(path=(RUN / p).as_posix(), sha256=sha(RUN / p)) for p in r['images']],
    task_owned_server_stopped=True, profile_preserved=profile.as_posix(), generated_site_files_unmodified=True,
    source_route_rendered_formulas=15, new_proof_note_formulas=8))
print('Actual14current images captured; ROOT must individually view before FINAL.')
