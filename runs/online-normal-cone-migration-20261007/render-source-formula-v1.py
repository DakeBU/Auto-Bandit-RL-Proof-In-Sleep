from common import *
import functools,http.server,threading,time
from PIL import Image
root=Path('.').resolve();site=root/'tmp/online-normal-cone-migration-site-v1'
edge=Path('C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe')
profile=root/'tmp/online-normal-cone-migration-formula-v1-profile'
png=root/'tmp/online-normal-cone-migration-formula-v1-full.png'
with (RUN/'formula-render-v1-server.log').open('w',encoding='utf-8') as log:
 class Handler(http.server.SimpleHTTPRequestHandler):
  def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
 server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)))
 thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start()
 command=[str(edge),'--headless=new','--disable-gpu','--no-first-run','--disable-sync','--disable-background-networking','--run-all-compositor-stages-before-draw','--user-data-dir='+str(profile),'--window-size=1440,7000','--hide-scrollbars','--virtual-time-budget=15000','--screenshot='+str(png),'http://127.0.0.1:'+str(server.server_port)+'/chapters/online-normal-cone/index.html']
 tick=time.monotonic()
 try:
  child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55)
  write(RUN/'formula-render-v1-edge.log',child.stdout);assert child.returncode==0 and png.is_file()
 finally:server.shutdown();server.server_close();thread.join(timeout=2)
with Image.open(png) as im:assert any(a!=b for a,b in im.getextrema());dims=im.size
write(RUN/'formula-render-v1.json',dict(status='nonblank-tall-viewport-captured-awaiting-pixel-review',snapshot=str(png),snapshot_sha256=sha(png),actual_dimensions=dims,actual_command=command,source_formula_count=3,elapsed_seconds=time.monotonic()-tick,profile_preserved=str(profile),server_stopped=True,generated_site_unmodified=True,source_only_source_commit=load(RUN/'registry-v1.json')['source_commit']))
print('Actual nonblank tall viewport captured; pixels still require direct visual review.')
