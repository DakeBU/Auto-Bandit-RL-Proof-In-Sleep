from common_reader_v2 import *
import functools, http.server, threading

fixed_integrated()
server = http.server.ThreadingHTTPServer(('127.0.0.1', 0),
    functools.partial(http.server.SimpleHTTPRequestHandler,
        directory=str(ROOT / 'tmp/online-completed-causal-site-v2')))
thread = threading.Thread(target=server.serve_forever, daemon=True); thread.start()
try:
    gate('overflow-diagnostic-v3', 'node', RUN / 'diagnose-reader-overflow-v3.cjs',
        'http://127.0.0.1:' + str(server.server_port) + '/chapters/online-foundations/index.html',
        RUN, ROOT / 'tmp/online-completed-causal-diagnostic-v3-profile')
finally:
    server.shutdown(); server.server_close(); thread.join(timeout=2)
