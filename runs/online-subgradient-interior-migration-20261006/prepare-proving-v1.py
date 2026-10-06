"""Require distinct source contract before actual contact-first proofs."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-INTERIOR-MIGRATION-20261006'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
r=load(run/'source-contract-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r.get('mathematical_repairs',r.get('required_mathematical_repairs',[])) and sha(r['report'])==r['report_sha256']
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
for row in load(run/'contract-source-inputs-v2.json')['rows']:assert reviewed[row['path']]==row['sha256'],row['path']
for p,h in reviewed.items():assert sha(p)==h,p
assert {n.rsplit('.',1)[-1] for n in r['target_verdicts']}==set(freeze['headers'])
for group in ['retained_module','fixed_shared_modules','fixed_old_canary']:
 for p,h in freeze[group].items():assert sha(p)==h,p
assert sha('Tests.lean')==freeze['Tests_append_only_original_sha256']
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),verdict=r['verdict'],report_sha256=r['report_sha256'],required_reader_corrections=r.get('required_reader_corrections',[]),retained_proofs=1,planned_new_proofs=2,new_proofs_compiled=0,body_accepted=False,source_terminal_accepted=False))
for event in ['stabilized','proving']:
 gate(event+'-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=freeze['headers'],source_contract_receipt=str(run/'source-contract-receipt-v1.json'),route='single lower relative affine contact then relative Riesz producer',first_ready_leaf='affine_support_of_relative_domain_interior',terminal='global supports at all specified relative-domain-interior points; prescribed-point affine contact retained',allowed_edits='append two frozen canonical proofs after originalnamespace block; ordinary leading comment; original ambientmodule bytes contiguous; fixed accepted sharedmodules/oldcanary/pins/Banditroot; new relativecanary+Testsimportappend and selectedreader',retained_proofs=1,planned_new_proofs=2,new_proofs_compiled=0,source_terminal_accepted=False,chapter_complete=False,goal_complete=False)))
ob=load(run/'proof-obligations-v1.json');ob['stage']='proving'
for row in ob['required']:row['state']='source-stabilized-ready-for-actual-new-proof' if not row['existing'] else 'source-stabilized-retained-revalidation-pending'
write('proof-obligations-proving-v1.json',ob)
write('preparation-read-path-errors-v1.md','Read-only lookup of prior prepare-body-v1.py failed because actual helper is prepare-body-review-v1.py, discovered with rg --files. No helper executed, no production edits or mathematical failure. Source preparer v1 failure/raw evidence recorded separately, actual v2 succeeds. All frozen terminals remain exact.')
print('Distinct source contract actually bound; contact-first proving starts, all2new bodies still pending.')
