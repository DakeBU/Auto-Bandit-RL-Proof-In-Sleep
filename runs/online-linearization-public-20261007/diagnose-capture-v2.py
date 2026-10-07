from common_v2 import *
import functools,http.server,threading
site=ROOT/'tmp/online-linearization-public-site-v1';page=site/'chapters/online-linearization/index.html';before=sha(page)
exe=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe');profile=ROOT/'tmp/online-linearization-public-diagnostics-v2-profile'
with (RUN/'capture-diagnostics-v2-server.log').open('w',encoding='utf-8') as log:
 class Handler(http.server.SimpleHTTPRequestHandler):
  def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
 server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)));thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start();tick=time.monotonic()
 url='http://127.0.0.1:'+str(server.server_port)+'/chapters/online-linearization/index.html';command=[str(exe),str(RUN/'diagnose-capture-v2.cjs'),url,str(RUN),str(profile)]
 try:
  child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55);write(RUN/'capture-diagnostics-v2-node.log',child.stdout);assert child.returncode==0
 finally:server.shutdown();server.server_close();thread.join(timeout=2)
assert sha(page)==before;print('Actual DOM diagnostics only; no image/formula-gate pass claimed.')
