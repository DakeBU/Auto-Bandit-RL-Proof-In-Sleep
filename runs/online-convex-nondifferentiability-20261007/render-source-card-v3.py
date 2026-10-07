from common_v4 import *
import functools,http.server,threading,time
site=ROOT/'tmp/online-convex-nondifferentiability-site-v1';page=site/'chapters/online-lipschitz/index.html';before=sha(page)
exe=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe');profile=ROOT/'tmp/online-convex-nondifferentiability-playwright-v2-profile'
with (RUN/'formula-render-v2-server.log').open('w',encoding='utf-8') as log:
 class Handler(http.server.SimpleHTTPRequestHandler):
  def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
 server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)));thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start();tick=time.monotonic()
 url='http://127.0.0.1:'+str(server.server_port)+'/chapters/online-lipschitz/index.html';command=[str(exe),str(RUN/'render-source-card-v3.cjs'),url,str(RUN),str(profile)]
 try:
  child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55);write(RUN/'formula-render-v2-node.log',child.stdout);assert child.returncode==0
 finally:server.shutdown();server.server_close();thread.join(timeout=2)
assert sha(page)==before
rendered=load(RUN/'formula-render-v2-browser.json');assert len(rendered['cards'])==3 and all(c['mathContainers']==1 and c['mathErrors']==0 for c in rendered['cards'])
write(RUN/'formula-render-v2.json',dict(status='actual-three-source-cards-rendered-awaiting-pixel-review',generated_page_sha256=before,site_source_commit=load(RUN/'registry-v2.json')['source_commit'],actual_command=command,elapsed_seconds=time.monotonic()-tick,DOM_sha256=sha(RUN/'formula-render-v2-dom.html'),browser_report_sha256=sha(RUN/'formula-render-v2-browser.json'),images=[dict(path=(RUN/('source-card-%02d-v2.png'%i)).as_posix(),sha256=sha(RUN/('source-card-%02d-v2.png'%i))) for i in [1,2,3]],task_owned_server_stopped=True,profile_preserved=profile.as_posix(),generated_site_unmodified=True))
print('THREE actual source cards visible/rendered in task-owned isolated Edge; fullcard actual pixel review pending.')
