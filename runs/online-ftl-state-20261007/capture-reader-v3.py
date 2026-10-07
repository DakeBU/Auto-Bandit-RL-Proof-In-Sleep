from common_v1 import *
import functools,http.server,threading
site=ROOT/'tmp/online-ftl-state-site-v3';page=site/'chapters/online-foundations/index.html';module=site/'modules/banditrlproof-onlinelearningftlstate/index.html';mean=site/'modules/banditrlproof-onlinelearningmean/index.html';before=[sha(page),sha(module),sha(mean)]
exe=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe');profile=ROOT/'tmp/online-ftl-state-playwright-v3-profile'
with (RUN/'formula-render-v3-server.log').open('w',encoding='utf-8') as log:
 class Handler(http.server.SimpleHTTPRequestHandler):
  def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
 server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)));thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start();tick=time.monotonic()
 url='http://127.0.0.1:'+str(server.server_port)+'/chapters/online-foundations/index.html';command=[str(exe),str(RUN/'capture-reader-v3.cjs'),url,str(RUN),str(profile),str(site/'books/registry.json')]
 try:
  child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55);write(RUN/'formula-render-v3-node.log',child.stdout);assert child.returncode==0
 finally:server.shutdown();server.server_close();thread.join(timeout=2)
assert [sha(page),sha(module),sha(mean)]==before
r=load(RUN/'formula-render-v3-browser.json');assert len(r['panels'])==18 and len(r['modulePanels'])==12 and all(c['mathErrors']==0 for c in r['panels'])
assert sum(c['mathContainers'] for c in r['panels'])==19 and len(r['images'])==31+2*len(r['scrollViews'])
write(RUN/'formula-render-v3.json',dict(status='Actual panels captured; root pixel review pending',generated_page_sha256=before[0],module_page_sha256=before[1],Mean_module_sha256=before[2],site_source_commit=load(RUN/'registry-v3.json')['source_commit'],actual_command=command,elapsed_seconds=time.monotonic()-tick,DOM_sha256=sha(RUN/'formula-render-v3-dom.html'),browser_report_sha256=sha(RUN/'formula-render-v3-browser.json'),images=[dict(path=(RUN/f).as_posix(),sha256=sha(RUN/f)) for f in r['images']],task_owned_server_stopped=True,profile_preserved=profile.as_posix(),generated_site_files_unmodified=True,source_route_rendered_formulas=10,new_public_note_formulas=9,actual_wide_scroll_pairs=len(r['scrollViews'])))
print('Actual',len(r['images']),'images captured; ROOT must view each before FINAL.')
