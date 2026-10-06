"""Actual reader screenshot with isolated task-owned headless Edge and local server."""
from pathlib import Path
import functools,hashlib,http.server,json,subprocess,threading,time
run=Path(__file__).resolve().parent;root=Path('.').resolve()
site=root/'tmp/online-affine-subgradient-migration-site-v1';snapshot=root/'tmp/online-affine-subgradient-migration-reader-v1.png'
profile=root/'tmp/online-affine-subgradient-migration-browser-v1-profile'
edge=Path('C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe')
assert edge.is_file() and (site/'chapters/online-affine-subgradient/index.html').is_file()
with (run/'browser-v1-server.log').open('w',encoding='utf-8') as log:
 class Handler(http.server.SimpleHTTPRequestHandler):
  def log_message(self,fmt,*args):log.write((fmt%args)+'\n');log.flush()
 server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)))
 thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start()
 command=[str(edge),'--headless=new','--disable-gpu','--no-first-run','--disable-sync','--disable-background-networking',
  '--user-data-dir='+str(profile),'--window-size=1440,1800','--hide-scrollbars','--virtual-time-budget=5000','--screenshot='+str(snapshot),
  'http://127.0.0.1:'+str(server.server_port)+'/chapters/online-affine-subgradient/index.html']
 start=time.monotonic()
 try:
  child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NO_WINDOW,timeout=55)
  (run/'browser-v1-edge.log').write_bytes(child.stdout)
 finally:server.shutdown();server.server_close();thread.join(timeout=2)
assert child.returncode==0 and snapshot.is_file()
with (run/'browser-v1-binding.json').open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(command=command,exit_code=child.returncode,elapsed_seconds=time.monotonic()-start,snapshot=str(snapshot),
  snapshot_sha256=hashlib.sha256(snapshot.read_bytes()).hexdigest(),scope='Actual first viewport only; no lower-fold pixel claim',
  profile_preserved=str(profile),server_owned=True,server_stopped=True),f,indent=2);f.write('\n')
print('Actual reader first viewport rendered; task server stopped; profile/screenshot retained.')
