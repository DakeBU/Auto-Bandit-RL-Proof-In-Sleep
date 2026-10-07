from common_v1 import *
import functools,http.server,threading
site=ROOT/'tmp/online-unit-scaling-public-site-v1';page=site/'chapters/online-unit-scaling/index.html';before=sha(page)
with (RUN/'algorithm-scroll-v1-server.log').open('w',encoding='utf-8') as log:
 class Handler(http.server.SimpleHTTPRequestHandler):
  def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
 server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)));thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start()
 url='http://127.0.0.1:'+str(server.server_port)+'/chapters/online-unit-scaling/index.html'
 command=['C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe',str(RUN/'capture-code-scroll-v1.cjs'),url,str(RUN),str(ROOT/'tmp/online-unit-scaling-public-code-scroll-v1-profile')]
 try:
  child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55);write(RUN/'algorithm-scroll-v1-node.log',child.stdout);assert child.returncode==0
 finally:server.shutdown();server.server_close();thread.join(timeout=2)
assert sha(page)==before
r=load(RUN/'algorithm-scroll-v1-browser.json');assert r['before']==0 and r['after']['scrollLeft']>0
write(RUN/'algorithm-scroll-v1.json',dict(status='actual-code-scroll-pair-pending-pixel-review',generated_page_sha256=before,site_source_commit=load(RUN/'registry-v1.json')['source_commit'],actual_command=command,browser_receipt_sha256=sha(RUN/'algorithm-scroll-v1-browser.json'),images=[dict(path=(RUN/f).as_posix(),sha256=sha(RUN/f)) for f in r['files']],generated_site_files_unmodified=True,actual_builtin_code_scroll_pixels=r['after']['scrollLeft'],actual_formula_overflow_pairs=0,task_server_stopped=True,source_or_statement_changed=False))
fixed(True);print('Actual builtin algorithm code scroll0->',r['after']['scrollLeft'],'px captured; no source/DOM/CSS/generated edits; pixel review pending.')
