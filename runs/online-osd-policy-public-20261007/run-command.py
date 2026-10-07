"""Unique actual-command log/receipt adapter; records exit only after completion."""
from pathlib import Path
import datetime,json,subprocess,sys,time
run=Path(__file__).resolve().parent;label=sys.argv[1];args=sys.argv[2:]
log=run/(label+'.log');receipt=run/(label+'-exit.json');assert not log.exists() and not receipt.exists()
start=datetime.datetime.now(datetime.timezone.utc).isoformat();begin=time.monotonic()
child=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
log.write_bytes(child.stdout)
receipt.write_text(json.dumps(dict(command=args,exit_code=child.returncode,started_at=start,ended_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),elapsed_seconds=round(time.monotonic()-begin,3)),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(label,'exit',child.returncode,'seconds',round(time.monotonic()-begin,3))
if child.returncode:print(child.stdout.decode('utf-8',errors='replace')[-3000:])
sys.exit(child.returncode)
