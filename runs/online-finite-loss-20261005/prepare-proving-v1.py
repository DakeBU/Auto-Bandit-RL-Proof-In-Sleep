"""Recheck distinct contract evidence before changing public proof surfaces."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-FINITE-LOSS-20261005'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
    p=run/n;assert not p.exists()
    with p.open('w',encoding='utf-8',newline='\n') as f:json.dump(x,f,indent=2);f.write('\n')
r=load(run/'source-contract-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer'
assert r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r['mathematical_repairs']
assert sha(r['report'])==r['report_sha256']
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
for row in load(run/'contract-source-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
for p,h in reviewed.items():assert sha(p)==h,p
assert set(n.rsplit('.',1)[-1] for n in r['target_verdicts'])==set(freeze['headers'])
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=r['report_sha256'],
    frozen_headers=freeze['headers'],verdict=r['verdict'],new_proofs_present=0,body_accepted=False))
for event in ['stabilized','proving']:
    subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),event+'-lifecycle-v1',sys.executable,'-X','utf8',
        'tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,
        frozen_headers=freeze['headers'],source_contract_receipt=str(run/'source-contract-receipt-v1.json'),
        route='single lower membership/EReal-case route',first_ready_leaf='finite_add_indicator_iff',
        allowed_edit_scope=load(run/'proof-obligations-v1.json')['edit_scope'],chapter_complete=False,goal_complete=False))],check=True)
ob=load(run/'proof-obligations-v1.json');ob['stage']='proving'
for row in ob['required']:row['state']='stabilized-proof-pending'
write('proof-obligations-proving-v1.json',ob)
print('Distinct contract/raw bindings verified; native stabilized/proving recorded.')
