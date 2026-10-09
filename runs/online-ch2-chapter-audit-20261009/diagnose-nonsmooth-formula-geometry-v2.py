from common_nonsmooth_publication_v4 import *
import functools,http.server,threading
fixed()
old=(RUN/'diagnose-nonsmooth-browser-v1.cjs').read_text('utf8')
old=old.replace("await page.waitForTimeout(1500);","await page.waitForTimeout(1500);\n  await page.evaluate(()=>document.querySelectorAll('#source-guide details').forEach(e=>e.open=true));")
before="text:e.textContent,containers:e.querySelectorAll('mjx-container').length"
after="text:e.textContent,containers:e.querySelectorAll('mjx-container').length,parentClientWidth:e.parentElement.clientWidth,parentScrollWidth:e.parentElement.scrollWidth,parentOverflowX:getComputedStyle(e.parentElement).overflowX,renderedWidth:e.querySelector('mjx-container')?.getBoundingClientRect().width||0"
assert old.count(before)==1;old=old.replace(before,after).replace('nonsmooth-browser-diagnostic-v1','nonsmooth-browser-diagnostic-v2')
js=RUN/'diagnose-nonsmooth-browser-v2.cjs';write(js,old)
profile=ROOT/'tmp/online-ch2-nonsmooth-playwright-diagnostic-v2-profile';assert not profile.exists()
node=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe')
class Handler(http.server.SimpleHTTPRequestHandler):
    def log_message(self,*args):pass
server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(SITE)))
thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start()
try:
    capture('nonsmooth-browser-diagnostic-command-v2',node,js,
        'http://127.0.0.1:'+str(server.server_port)+'/chapters/online-subgradient-differentiability/index.html',RUN,profile)
finally:
    server.shutdown();server.server_close();thread.join(timeout=2)
fixed()
print('Actual opened-source formula geometry captured without editing source/generated files.')
