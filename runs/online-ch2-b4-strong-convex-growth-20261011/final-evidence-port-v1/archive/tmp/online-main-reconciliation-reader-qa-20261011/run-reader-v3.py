from pathlib import Path
import json,subprocess,hashlib,datetime,sys
r=Path.cwd();d=r/'tmp/online-main-reconciliation-reader-qa-20261011';head=sys.argv[1];h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();helper=d/'capture-reconciliation-reader-v9.cjs'
assert h(helper)=='5585639863740df5d896865fc9f3f7369f9f094c75d759c66d8a724bc32eb3c6'
review=r/'tmp/online-main-reconciliation-helper-independent-review-20261011/independent-helper-review-v4.json';assert h(review)=='8597c2179b72f345f2cb33296af1cc55de4952c08a070df62dd79a9ebb8f0509';rv=json.loads(review.read_bytes());assert rv['verdict']=='accepted-prepared-reader-helper' and rv['blocking_repairs']==[]
gate=r/'tmp/online-main-reconciliation-gates-20261011/full-harness-v5/receipt.json';g=json.loads(gate.read_bytes());assert g['actual_exit']==0 and g['capture_integrity_ok'] is True and g['pre_git']['HEAD']==head
for role in ['site-build','site-check']:
 q=json.loads((r/('tmp/online-main-reconciliation-gates-20261011/'+role+'-v5/receipt.json')).read_bytes());assert q['actual_exit']==0 and q['capture_integrity_ok'] is True and q['pre_git']['HEAD']==head
site=r/'tmp/online-main-reconciliation-site-20261011-v5';argv=['C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe',str(helper),'http://127.0.0.1:8894/chapters/online-ogd/',str(d/'actual-v3'),str(d/'profile-v3'),str(site/'books/registry.json'),str(r),str(site),str(gate),h(gate),head]
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (d/'execution-v3.stdout.raw').open('xb') as o,(d/'execution-v3.stderr.raw').open('xb') as e:p=subprocess.run(argv,cwd=r,stdout=o,stderr=e)
row={'argv':argv,'start_utc':start,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actual_exit_code':p.returncode,'helper_sha256':h(helper),'independent_review_sha256':h(review),'stdout_sha256':h(d/'execution-v3.stdout.raw'),'stderr_sha256':h(d/'execution-v3.stderr.raw'),'scope':'Actual isolated local reader execution only; original-pixel and independent final review still required.'}
with (d/'execution-receipt-v3.json').open('xb') as f:f.write((json.dumps(row,indent=2)+'\n').encode())
print(json.dumps(row,indent=2));sys.exit(p.returncode)
