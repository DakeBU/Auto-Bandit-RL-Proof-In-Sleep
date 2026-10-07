from common_v2 import *
import functools,http.server,threading
site=ROOT/'tmp/online-linearization-public-site-v1';page=site/'chapters/online-linearization/index.html';before=sha(page)
exe=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe');profile=ROOT/'tmp/online-linearization-public-scroll-v4-profile'
with (RUN/'formula-scroll-v4-server.log').open('w',encoding='utf-8') as log:
 class Handler(http.server.SimpleHTTPRequestHandler):
  def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
 server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)));thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start();tick=time.monotonic()
 url='http://127.0.0.1:'+str(server.server_port)+'/chapters/online-linearization/index.html';command=[str(exe),str(RUN/'capture-formula-scroll-v4.cjs'),url,str(RUN),str(profile)]
 try:
  child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55);write(RUN/'formula-scroll-v4-node.log',child.stdout);assert child.returncode==0
 finally:server.shutdown();server.server_close();thread.join(timeout=2)
assert sha(page)==before
r=load(RUN/'formula-scroll-v4-browser.json');assert r['after']['left']>0 and r['after']['MathJaxErrors']==0
files=['proof-bridge-step4-left-v4.png','proof-bridge-step4-right-v4.png']
write(RUN/'formula-scroll-v4.json',dict(status='actual-left-right-horizontal-scroll-awaiting-pixel-review',actual_command=command,generated_page_sha256=before,site_source_commit=load(RUN/'registry-v1.json')['source_commit'],browser_report_sha256=sha(RUN/'formula-scroll-v4-browser.json'),images=[dict(path=(RUN/f).as_posix(),sha256=sha(RUN/f)) for f in files],actual_scroll_only=True,no_source_DOM_CSS_or_generated_file_edit=True,profile_preserved=profile.as_posix(),task_owned_server_stopped=True))
print('Actual left/right formula scroll captured; both pixel views pending, site/DOM/CSS unchanged.')
