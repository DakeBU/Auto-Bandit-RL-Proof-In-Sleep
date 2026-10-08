from common_reader_v2 import *
import functools,http.server,threading
fixed_integrated()
site=ROOT/'tmp/online-ae-causal-site-v2'
reg=load(RUN/'registry-v2.json')
files=[site/'chapters/online-foundations/index.html']+[site/p for p in reg['module_HTML_sha256']]
before={p.as_posix():sha(p) for p in files}
node=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe')
profile=ROOT/'tmp/online-ae-causal-playwright-v2-profile'
prior=load(ROOT/'runs/online-c1-core-audit-20261008/formula-render-v2-browser.json')
assert not (RUN/'formula-render-v2-server.log').exists()
with (RUN/'formula-render-v2-server.log').open('w',encoding='utf8') as log:
    class Handler(http.server.SimpleHTTPRequestHandler):
        def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)))
    thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start();tick=time.monotonic()
    url='http://127.0.0.1:'+str(server.server_port)+'/chapters/online-foundations/index.html'
    command=[str(node),str(RUN/'capture-reader-v2.cjs'),url,str(RUN),str(profile),str(site/'books/registry.json'),
        str(CONTRACT/'targets-v1.json'),str(reg['source_cards']),str(prior['actualSourceGuideMathContainers']+1)]
    try:
        child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55)
        write(RUN/'formula-render-v2-node.log',child.stdout)
        write(RUN/'formula-render-v2-node-exit.json',dict(command=command,actual_exit=child.returncode,
            seconds=time.monotonic()-tick,log_sha256=sha(RUN/'formula-render-v2-node.log')))
        assert child.returncode==0,child.stdout.decode('utf8',errors='replace')
    finally:server.shutdown();server.server_close();thread.join(timeout=2)
assert {p.as_posix():sha(p) for p in files}==before
r=load(RUN/'formula-render-v2-browser.json')
assert len(r['panels'])==4 and len(r['modulePanels'])==3 and len(r['images'])==8
assert not r['sourceHorizontalScrollers'] and all(p['mathErrors']==0 for p in r['panels'])
write(RUN/'formula-render-v2.json',dict(status='8 actual original current images captured; ROOT and distinct FINAL pixel inspections pending',
    source_commit=reg['source_commit'],generated_HTML_sha256=before,actual_command=command,
    DOM_sha256=sha(RUN/'formula-render-v2-dom.html'),browser_report_sha256=sha(RUN/'formula-render-v2-browser.json'),
    images=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in r['images']],
    task_owned_server_stopped=True,profile_preserved=profile.as_posix(),generated_site_files_unmodified=True,
    chapter_complete=False,goal_complete=False))
fixed_integrated()
print('Actual 8 original panels captured; separate original pixel inspection still required.',flush=True)
