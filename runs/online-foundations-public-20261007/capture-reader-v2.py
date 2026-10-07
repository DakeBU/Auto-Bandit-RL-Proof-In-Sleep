from common_v1 import *
import functools,http.server,threading
site=ROOT/'tmp/online-foundations-public-site-v2';page=site/'chapters/online-foundations/index.html';module=site/'modules/banditrlproof-onlinelearningfoundations/index.html';before=[sha(page),sha(module)]
exe=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe');profile=ROOT/'tmp/online-foundations-public-playwright-v2-profile'
with (RUN/'formula-render-v2-server.log').open('w',encoding='utf-8') as log:
 class Handler(http.server.SimpleHTTPRequestHandler):
  def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
 server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)));thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start();tick=time.monotonic()
 url='http://127.0.0.1:'+str(server.server_port)+'/chapters/online-foundations/index.html';command=[str(exe),str(RUN/'capture-reader-v2.cjs'),url,str(RUN),str(profile)]
 try:
  child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55);write(RUN/'formula-render-v2-node.log',child.stdout);assert child.returncode==0
 finally:server.shutdown();server.server_close();thread.join(timeout=2)
assert [sha(page),sha(module)]==before
rendered=load(RUN/'formula-render-v2-browser.json');assert len(rendered['panels'])==7 and all(c['mathErrors']==0 for c in rendered['panels'])
assert sum(c['mathContainers'] for c in rendered['panels'])==8
files=rendered['images'];assert len(files)==9+2*len(rendered['scrollViews'])
write(RUN/'formula-render-v2.json',dict(status='Actual panels captured; root pixel review pending',generated_page_sha256=before[0],module_page_sha256=before[1],site_source_commit=load(RUN/'registry-v2.json')['source_commit'],actual_command=command,elapsed_seconds=time.monotonic()-tick,DOM_sha256=sha(RUN/'formula-render-v2-dom.html'),browser_report_sha256=sha(RUN/'formula-render-v2-browser.json'),images=[dict(path=(RUN/f).as_posix(),sha256=sha(RUN/f)) for f in files],task_owned_server_stopped=True,profile_preserved=profile.as_posix(),generated_site_files_unmodified=True,source_route_rendered_formulas=7,public_note_rendered_formula=1,data_math_fields=7,actual_wide_scroll_pair_count=len(rendered['scrollViews'])))
print('Actual',len(files),'reader/source/module images;7 source-guide formulas +1 public note; pixel review separately pending.')
