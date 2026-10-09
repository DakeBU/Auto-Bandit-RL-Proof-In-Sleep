from common_nonsmooth_publication_v2 import *
import functools,http.server,threading

fixed()
reg=load(RUN/'nonsmooth-registry-inspected-v1.json')
files=[SITE/'chapters/online-subgradient-differentiability/index.html']+[SITE/p for p in reg['module_HTML_sha256']]
before={p.as_posix():sha(p) for p in files}
node=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe')
profile=ROOT/'tmp/online-ch2-nonsmooth-playwright-v1-profile'
assert not profile.exists() and not list(RUN.glob('reader-first-viewport-v1.png'))
with (RUN/'nonsmooth-browser-server-v1.log').open('x',encoding='utf8') as log:
    class Handler(http.server.SimpleHTTPRequestHandler):
        def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(SITE)))
    thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start()
    url='http://127.0.0.1:'+str(server.server_port)+'/chapters/online-subgradient-differentiability/index.html'
    args=[node,RUN/'capture-nonsmooth-reader-v1.cjs',url,RUN,profile,SITE/'books/registry.json',
        CONTRACT/'nonsmooth-targets-draft-v1.json',str(reg['source_cards']),str(reg['source_cards'])]
    try:
        code,stdout=capture('nonsmooth-browser-node-v1',*args)
    finally:
        server.shutdown();server.server_close();thread.join(timeout=2)
assert {p.as_posix():sha(p) for p in files}==before
r=load(RUN/'formula-render-v1-browser.json')
assert len(r['panels'])==4 and len(r['modulePanels'])==3 and len(r['images'])==8
assert not r['errors'] and not r['failed'] and not r['sourceHorizontalScrollers']
assert all(p['mathContainers']==1 and p['mathErrors']==0 for p in r['panels'])
write(RUN/'nonsmooth-browser-capture-inspected-v1.json',dict(
    state='Eight actual current images captured, formalizer and distinct FINAL personal pixel inspection pending',
    source_commit=reg['source_commit'],generated_HTML_sha256=before,
    actual_browser_report_sha256=sha(RUN/'formula-render-v1-browser.json'),
    actual_DOM_sha256=sha(RUN/'formula-render-v1-dom.html'),
    images=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in r['images']],
    task_owned_server_stopped=True,profile_preserved=profile.as_posix(),generated_site_files_unmodified=True,
    chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Eight actual current browser images/DOM captured; both personal pixel reviews remain separate.')
