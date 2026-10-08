from common_integrated_v2 import *
import functools, http.server, threading

fixed_integrated()
site = ROOT / 'tmp/online-iid-benchmark-site-v2'
page = site / 'chapters/online-foundations/index.html'
module = site / load(RUN / 'registry-v2.json')['module_path']
before = [sha(page), sha(module)]
exe = Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe')
profile = ROOT / 'tmp/online-iid-benchmark-playwright-v1-profile'
with (RUN / 'overflow-diagnostic-v3-server.log').open('w', encoding='utf8') as log:
    class Handler(http.server.SimpleHTTPRequestHandler):
        def log_message(self, fmt, *args): log.write((fmt % args) + '\n'); log.flush()
    server = http.server.ThreadingHTTPServer(('127.0.0.1', 0), functools.partial(Handler, directory=str(site)))
    thread = threading.Thread(target=server.serve_forever, daemon=True); thread.start(); tick=time.monotonic()
    url = 'http://127.0.0.1:' + str(server.server_port) + '/chapters/online-foundations/index.html'
    command = [str(exe), str(RUN / 'capture-overflow-diagnostic-v3.cjs'), url, str(RUN), str(profile), str(site / 'books/registry.json')]
    try:
        child = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, creationflags=subprocess.CREATE_NO_WINDOW, timeout=55)
        write(RUN / 'overflow-diagnostic-v3-node.log', child.stdout)
        assert child.returncode == 0, child.stdout.decode('utf8', errors='replace')
    finally:
        server.shutdown(); server.server_close(); thread.join(timeout=2)
