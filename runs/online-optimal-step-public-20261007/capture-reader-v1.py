from common_v1 import *
import functools,http.server,threading
site=ROOT/'tmp/online-optimal-step-public-site-v1';page=site/'chapters/online-optimal-step/index.html';before=sha(page)
exe=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe');profile=ROOT/'tmp/online-optimal-step-public-playwright-v1-profile'
with (RUN/'formula-render-v1-server.log').open('w',encoding='utf-8') as log:
 class Handler(http.server.SimpleHTTPRequestHandler):
  def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
 server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)));thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start();tick=time.monotonic()
 url='http://127.0.0.1:'+str(server.server_port)+'/chapters/online-optimal-step/index.html';command=[str(exe),str(RUN/'capture-reader-v1.cjs'),url,str(RUN),str(profile)]
 try:
  child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55);write(RUN/'formula-render-v1-node.log',child.stdout);assert child.returncode==0
 finally:server.shutdown();server.server_close();thread.join(timeout=2)
assert sha(page)==before;rendered=load(RUN/'formula-render-v1-browser.json');assert len(rendered['panels'])==5 and sum(c['mathContainers'] for c in rendered['panels'])==12 and all(c['mathErrors']==0 for c in rendered['panels'])
files=rendered['images'];assert len(files)==6+2*len(rendered['scrollViews'])
write(RUN/'formula-render-v1.json',dict(status='actual-six-panels-plus-any-wide-scroll-pairs-awaiting-pixel-review',generated_page_sha256=before,site_source_commit=load(RUN/'registry-v1.json')['source_commit'],actual_command=command,elapsed_seconds=time.monotonic()-tick,DOM_sha256=sha(RUN/'formula-render-v1-dom.html'),browser_report_sha256=sha(RUN/'formula-render-v1-browser.json'),images=[dict(path=(RUN/f).as_posix(),sha256=sha(RUN/f)) for f in files],task_owned_server_stopped=True,profile_preserved=profile.as_posix(),generated_site_files_unmodified=True,source_route_rendered_formulas=12,data_math_fields=15,three_algorithm_steps_rendered_as_prose=True,actual_wide_scroll_pair_count=len(rendered['scrollViews'])))
print('Actual6 panel images +',2*len(rendered['scrollViews']),'wide-scroll views;12 rendered formulas; actual pixel review separate pending.')
