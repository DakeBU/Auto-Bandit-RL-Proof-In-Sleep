"""Bind exact generated three-case TeX and actually render source card in isolated Edge."""
from common import *
import functools,http.server,threading,time,html
root=Path('.').resolve();site=root/'tmp/online-subgradient-absolute-migration-site-v2'
page=site/'chapters/online-subgradient-absolute/index.html'
raw=page.read_text(encoding='utf-8');card=re.search(r'<article class="source-theorem-card">(.*?)</article>',raw,re.S).group(1)
tex=html.unescape(re.search(r'<span class="math-tex"[^>]*>(.*?)</span>',card,re.S).group(1))
repair=load(RUN/'reader-formula-repair-v2.json');assert tex==repair['actual_normalizer_output']
assert tex.count('\\\\')==2 and '{[-1,1]}' in tex and all(s in tex for s in ['&x>0','&x=0','&x<0'])
edge=Path('C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe');assert edge.is_file()
profile=root/'tmp/online-subgradient-absolute-migration-formula-v2-profile'
png=root/'tmp/online-subgradient-absolute-migration-formula-v2.png';dom=RUN/'formula-render-v2-dom.html'
with (RUN/'formula-render-v2-server.log').open('w',encoding='utf-8') as log:
 class Handler(http.server.SimpleHTTPRequestHandler):
  def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
 server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)))
 thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start()
 url='http://127.0.0.1:'+str(server.server_port)+'/chapters/online-subgradient-absolute/index.html#proof-bridge'
 base=[str(edge),'--headless=new','--disable-gpu','--no-first-run','--disable-sync','--disable-background-networking','--user-data-dir='+str(profile),'--window-size=1440,1800','--hide-scrollbars','--virtual-time-budget=20000']
 commands=[];tick=time.monotonic()
 try:
  command=base+['--screenshot='+str(png),url];commands.append(command)
  child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55)
  write(RUN/'formula-render-v2-edge.log',child.stdout);assert child.returncode==0 and png.is_file()
  command=base+['--dump-dom',url];commands.append(command)
  child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55)
  write(dom,child.stdout);write(RUN/'formula-render-v2-dom-edge.log',child.stderr);assert child.returncode==0
 finally:server.shutdown();server.server_close();thread.join(timeout=2)
runtime=dom.read_text(encoding='utf-8');runtimecard=re.search(r'<article class="source-theorem-card">(.*?)</article>',runtime,re.S).group(1)
rendered='mjx-container' in runtimecard
assert rendered,'MathJax source-card rendering unavailable; raw source TeX alone is insufficient for this render gate'
assert runtimecard.count('<mjx-mtr')==3,('Expected three rendered rows',runtimecard.count('<mjx-mtr'))
write(RUN/'formula-render-v2.json',dict(status='generated-TeX-and-rendered-three-row-MathJax-passed',actual_generated_tex=tex,generated_page_sha256=sha(page),DOM=dom.as_posix(),DOM_sha256=sha(dom),rendered_source_card=True,rendered_case_rows=3,snapshot=str(png),snapshot_sha256=sha(png),commands=commands,elapsed_seconds=time.monotonic()-tick,profile_preserved=str(profile),server_stopped=True,pixel_review_pending=True,scope='Source formula anchor viewport and dumped actual rendered DOM only; visual inspection remains separate.'))
print('Exact source formula and three actual MathJax case rows rendered; screenshot awaits separate pixel inspection.')
