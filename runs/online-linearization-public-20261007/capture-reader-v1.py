from common_v2 import *
import functools,http.server,threading
site=ROOT/'tmp/online-linearization-public-site-v1';page=site/'chapters/online-linearization/index.html';before=sha(page)
exe=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe');profile=ROOT/'tmp/online-linearization-public-playwright-v1-profile'
with (RUN/'formula-render-v1-server.log').open('w',encoding='utf-8') as log:
 class Handler(http.server.SimpleHTTPRequestHandler):
  def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
 server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)));thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start();tick=time.monotonic()
 url='http://127.0.0.1:'+str(server.server_port)+'/chapters/online-linearization/index.html';command=[str(exe),str(RUN/'capture-reader-v1.cjs'),url,str(RUN),str(profile)]
 try:
  child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55);write(RUN/'formula-render-v1-node.log',child.stdout);assert child.returncode==0
 finally:server.shutdown();server.server_close();thread.join(timeout=2)
assert sha(page)==before;rendered=load(RUN/'formula-render-v1-browser.json');assert len(rendered['panels'])==4 and sum(c['mathContainers'] for c in rendered['panels'])==13 and all(c['mathErrors']==0 for c in rendered['panels'])
files=['reader-first-viewport-v1.png','source-card-01-v1.png','algorithm-v1.png','proof-bridge-v1.png','worked-example-v1.png']
write(RUN/'formula-render-v1.json',dict(status='actual-five-images-thirteen-route-formulas-awaiting-pixel-review',generated_page_sha256=before,site_source_commit=load(RUN/'registry-v1.json')['source_commit'],actual_command=command,elapsed_seconds=time.monotonic()-tick,DOM_sha256=sha(RUN/'formula-render-v1-dom.html'),browser_report_sha256=sha(RUN/'formula-render-v1-browser.json'),images=[dict(path=(RUN/f).as_posix(),sha256=sha(RUN/f)) for f in files],task_owned_server_stopped=True,profile_preserved=profile.as_posix(),generated_site_files_unmodified=True))
print('Actual firstviewport/sourcecard/fullalgorithm/bridge/example thirteen formulas rendered; five pixel views separate pending.')
