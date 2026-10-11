from pathlib import Path
import json,subprocess,hashlib,datetime,sys
r=Path.cwd();d=r/'tmp/online-main-reconciliation-reader-qa-20261011';report=json.loads((d/'preparation-report-v2.json').read_bytes());argv=report['required_argv'];assert hashlib.sha256(Path(argv[1]).read_bytes()).hexdigest()=='c09b3f724d30c6bf736839e9581565b76570a918ca88214fcf2b285830cca2e9'
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (d/'execution-v1.stdout.raw').open('xb') as o,(d/'execution-v1.stderr.raw').open('xb') as e:p=subprocess.run(argv,cwd=r,stdout=o,stderr=e)
row={'argv':argv,'start_utc':start,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actual_exit_code':p.returncode,'helper_sha256':hashlib.sha256(Path(argv[1]).read_bytes()).hexdigest(),'stdout_sha256':hashlib.sha256((d/'execution-v1.stdout.raw').read_bytes()).hexdigest(),'stderr_sha256':hashlib.sha256((d/'execution-v1.stderr.raw').read_bytes()).hexdigest(),'scope':'Actual browser execution, independent and parent original-pixel review still required.'};(d/'execution-receipt-v1.json').write_bytes((json.dumps(row,indent=2)+'\n').encode());print(json.dumps(row,indent=2));sys.exit(p.returncode)
