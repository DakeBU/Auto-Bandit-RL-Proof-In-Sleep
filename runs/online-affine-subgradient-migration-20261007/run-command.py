"""Preserve raw command evidence, with bounded failure output and portable UTF-8."""
from pathlib import Path
import subprocess,sys,json,datetime,time
sys.stdout.reconfigure(encoding='utf-8')
root=Path(__file__).resolve().parent
label=sys.argv[1];cmd=sys.argv[2:]
assert not (root/(label+'.log')).exists() and not (root/(label+'-exit.json')).exists(), 'Evidence labels are immutable; choose a new attempt version'
start=datetime.datetime.now(datetime.timezone.utc).isoformat();tick=time.monotonic()
p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(root/(label+'.log')).write_bytes(p.stdout)
with (root/(label+'-exit.json')).open('w',encoding='utf-8',newline='\n') as f:
    json.dump({'command':cmd,'exit_code':p.returncode,'started_at':start,'ended_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick},f,indent=2);f.write('\n')
print(label,'exit',p.returncode,'seconds',round(time.monotonic()-tick,3))
if p.returncode:
    print('Failure tail only; full raw output is retained in',label+'.log')
    print(p.stdout.decode('utf-8',errors='replace')[-2400:])
sys.exit(p.returncode)
