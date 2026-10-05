"""Render the actual reader in a task-owned isolated headless Edge profile."""
from pathlib import Path
import functools,hashlib,http.server,json,subprocess,threading,time
run=Path(__file__).resolve().parent
root=Path('.').resolve()
site=root/'tmp/online-finite-loss-site-v3'
snapshot=root/'tmp/online-finite-loss-reader-v3.png'
profile=root/'tmp/online-finite-loss-browser-v3-profile'
edge=Path('C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe')
assert edge.is_file() and (site/'chapters/online-convex/index.html').is_file()
with (run/'browser-v3-server.log').open('w',encoding='utf-8') as log:
    class Handler(http.server.SimpleHTTPRequestHandler):
        def log_message(self,fmt,*args):
            log.write((fmt%args)+'\n');log.flush()
    server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(Handler,directory=str(site)))
    thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start()
    command=[str(edge),'--headless=new','--disable-gpu','--no-first-run','--disable-sync',
        '--disable-background-networking','--user-data-dir='+str(profile),'--window-size=1440,1800',
        '--hide-scrollbars','--virtual-time-budget=5000','--screenshot='+str(snapshot),
        'http://127.0.0.1:'+str(server.server_port)+'/chapters/online-convex/index.html']
    start=time.monotonic()
    try:
        child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
            creationflags=subprocess.CREATE_NO_WINDOW,timeout=55)
        (run/'browser-v3-edge.log').write_bytes(child.stdout)
    finally:
        server.shutdown();server.server_close();thread.join(timeout=2)
assert child.returncode==0 and snapshot.is_file(),child.stdout.decode('utf-8',errors='replace')
binding=dict(command=command,exit_code=child.returncode,elapsed_seconds=time.monotonic()-start,
    snapshot=str(snapshot),snapshot_sha256=hashlib.sha256(snapshot.read_bytes()).hexdigest(),
    scope='Actual first viewport only; no lower-fold pixel claim',profile_preserved=str(profile),
    server_owned=True,server_stopped=True)
with (run/'browser-v3-binding.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(binding,f,indent=2);f.write('\n')
print('Actual reader screenshot saved; isolated profile retained; task-owned server stopped.')
