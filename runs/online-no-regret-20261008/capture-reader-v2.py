from common_integrated_v2 import *
import functools,http.server,threading
fixed_integrated()
site=ROOT/'tmp/online-no-regret-site-v1';page=site/'chapters/online-foundations/index.html';module=site/load(RUN/'registry-v1.json')['module_path'];before=[sha(page),sha(module)]
exe=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe');profile=ROOT/'tmp/online-no-regret-playwright-v1-profile'
with (RUN/'formula-render-v1-server.log').open('w',encoding='utf8') as log:
 class Handler(http.server.SimpleHTTPRequestHandler):
  def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
 server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)));thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start();tick=time.monotonic()
 url='http://127.0.0.1:'+str(server.server_port)+'/chapters/online-foundations/index.html';command=[str(exe),str(RUN/'capture-reader-v1.cjs'),url,str(RUN),str(profile),str(site/'books/registry.json')]
 try:
  child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55);write(RUN/'formula-render-v1-node.log',child.stdout);assert child.returncode==0
 finally:server.shutdown();server.server_close();thread.join(timeout=2)
assert [sha(page),sha(module)]==before
r=load(RUN/'formula-render-v1-browser.json');assert len(r['panels'])==7 and len(r['modulePanels'])==4 and len(r['images'])==12
assert all(c['mathErrors']==0 for c in r['panels']) and not r['sourceHorizontalScrollers']
write(RUN/'formula-render-v1.json',dict(status='Actual12current panels captured; root pixel review pending',generated_page_sha256=before[0],module_page_sha256=before[1],site_source_commit=load(RUN/'registry-v1.json')['source_commit'],actual_command=command,elapsed_seconds=time.monotonic()-tick,DOM_sha256=sha(RUN/'formula-render-v1-dom.html'),browser_report_sha256=sha(RUN/'formula-render-v1-browser.json'),images=[dict(path=(RUN/f).as_posix(),sha256=sha(RUN/f)) for f in r['images']],task_owned_server_stopped=True,profile_preserved=profile.as_posix(),generated_site_files_unmodified=True,source_route_rendered_formulas=13,new_public_note_formulas=6))
print('Actual12current images captured; ROOT must view each before FINAL.')
