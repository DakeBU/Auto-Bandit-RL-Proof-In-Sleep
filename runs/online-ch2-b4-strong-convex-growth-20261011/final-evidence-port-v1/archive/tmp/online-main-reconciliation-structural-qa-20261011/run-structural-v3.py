from pathlib import Path
import json,hashlib,subprocess,sys
r=Path.cwd();d=r/'tmp/online-main-reconciliation-structural-qa-20261011';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();head='3007a59126196279430079a1030727aec53ea807'
helper=d/'check-reconciliation-structure-v3.py';assert h(helper)=='879ec5df108e5d1585686fbae7bbcb5fb30f1a91e3943dfae83c0d9e7386e009'
gate=r/'tmp/online-main-reconciliation-gates-20261011/full-harness-v4/receipt.json';g=json.loads(gate.read_bytes());assert g['actual_exit']==0 and g['capture_integrity_ok'] is True and g['pre_git']['HEAD']==head
for role in ['site-build','site-check']:
 q=json.loads((r/('tmp/online-main-reconciliation-gates-20261011/'+role+'-v4/receipt.json')).read_bytes());assert q['actual_exit']==0 and q['capture_integrity_ok'] is True and q['pre_git']['HEAD']==head
spec=json.loads((d/'input-spec-prepared-v2.json').read_bytes());spec.update(ready_for_execution=True,head=head,checker_sha256=h(helper),recorder_sha256='bafe784fad8810f866105ffd19e3504f70ebf1e28949611549d584630a5b7ce8');assert spec['allowed_old_object_deltas']==[]
p=d/'input-spec-execution-v3.json'
with p.open('xb') as f:f.write((json.dumps(spec,indent=2)+'\n').encode())
argv=['C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe','-B','-X','utf8',str(helper),'--root',str(r),'--baseline',str(r/'tmp/online-ch2-b4-finite-identity-site-20261011-v1/books/registry.json'),'--site',str(r/'tmp/online-main-reconciliation-site-20261011-v4'),'--gate',str(gate),'--spec',str(p),'--output',str(d/'actual-v3.json'),'--spec-sha256',h(p),'--gate-sha256',h(gate),'--head',head]
with (d/'execution-v3.stdout.raw').open('xb') as o,(d/'execution-v3.stderr.raw').open('xb') as e:proc=subprocess.run(argv,cwd=r,stdout=o,stderr=e)
row={'argv':argv,'actual_exit_code':proc.returncode,'helper_sha256':h(helper),'spec_sha256':h(p),'stdout_sha256':h(d/'execution-v3.stdout.raw'),'stderr_sha256':h(d/'execution-v3.stderr.raw')}
with (d/'execution-receipt-v3.json').open('xb') as f:f.write((json.dumps(row,indent=2)+'\n').encode())
print(json.dumps(row));sys.exit(proc.returncode)
