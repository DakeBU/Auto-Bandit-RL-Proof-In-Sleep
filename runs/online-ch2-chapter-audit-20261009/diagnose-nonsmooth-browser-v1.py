from common_nonsmooth_publication_v4 import *
import functools,http.server,threading,base64
fixed()
receipt=load(RUN/'nonsmooth-browser-node-v1.json')
assert receipt['actual_exit']==1
write(RUN/'nonsmooth-browser-initial-failure-v1.json',dict(actual_receipt_sha256=sha(RUN/'nonsmooth-browser-node-v1.json'),
    actual_exit=1,actual_message=base64.b64decode(receipt['stdout_base64']).decode('utf8'),
    classification='browser-source-MathJax-count-timeout-under-diagnosis',
    no_successful_capture_or_pixel_claim=True,failed_profile_preserved='tmp/online-ch2-nonsmooth-playwright-v1-profile',
    site_and_proofs_unchanged=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
node=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe')
profile=ROOT/'tmp/online-ch2-nonsmooth-playwright-diagnostic-v1-profile';assert not profile.exists()
class Handler(http.server.SimpleHTTPRequestHandler):
    def log_message(self,*args):pass
server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(SITE)))
thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start()
try:
    capture('nonsmooth-browser-diagnostic-command-v1',node,RUN/'diagnose-nonsmooth-browser-v1.cjs',
        'http://127.0.0.1:'+str(server.server_port)+'/chapters/online-subgradient-differentiability/index.html',RUN,profile)
finally:
    server.shutdown();server.server_close();thread.join(timeout=2)
fixed()
print('Actual browser diagnostics captured; no generated/source edit, both failed and diagnostic profiles preserved.')
