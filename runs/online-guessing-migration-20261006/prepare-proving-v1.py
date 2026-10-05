"""Only enter proof work after distinct source stabilization; retain exact previous bytes."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-GUESSING-MIGRATION-20261006'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
r=load(run/'source-contract-receipt-v1.json');freeze=load(run/'draft-freeze-v2.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r.get('mathematical_repairs',r.get('required_mathematical_repairs',[])) and sha(r['report'])==r['report_sha256']
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
for row in load(run/'contract-source-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
for p,h in reviewed.items():assert sha(p)==h,p
assert {n.rsplit('.',1)[-1] for n in r['target_verdicts']}==set(freeze['headers'])
for p,h in dict(freeze['module'],**freeze['canary']).items():assert sha(p)==h,p
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),verdict=r['verdict'],report_sha256=r['report_sha256'],required_reader_corrections=r.get('required_reader_corrections',[]),retained_proofs=9,retained_definitions=1,new_targets=3,new_bodies_compiled=False,source_package_accepted=False))
snapshots=[]
for p in list(freeze['module'])+['BanditRLProof.lean','Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:
 dest=run/'leaves'/('pre-integration-'+p.replace('/','--')+'.txt');assert not dest.exists();dest.write_bytes(Path(p).read_bytes())
 snapshots.append(dict(path=p,snapshot=dest.as_posix(),raw_sha256=sha(dest),authorized_delta='leading source/scope comment only, all original proof tokens/context fixed' if p in freeze['module'] else 'single new shared comparison import' if p=='BanditRLProof.lean' else 'single new public comparison canary import' if p=='Tests.lean' else 'only online-guessing-ogd reader subtree'))
write('historical-raw-supersession-v1.json',dict(rows=snapshots,previous_accepted_packages_immutable=True,exact_current_raw_bytes_preserved=True))
for event in ['stabilized','proving']:
 gate(event+'-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,fingerprint_version='native-v2-whitespace-only-correction',frozen_headers=freeze['headers'],source_contract_receipt=str(run/'source-contract-receipt-v1.json'),first_ready_leaf='meanPredict_zero_cumulativeLoss',terminal='guessing_vs_mean_unbounded:forallC,Nexistsn>N actual loss gap>C',route='single lower zero-prefix sum then gap then Archimedean witness',allowed_edits='three frozen new theorem bodies/new canary/root/Tests import; retained9headers/proof tokens/unitInterval fixed/oldcanaries bytefixed/leading comments and only selected reader subtree',retained_proofs=9,retained_definitions=1,new_proofs_pending=3,source_package_accepted=False,chapter_complete=False,goal_complete=False)))
write('proof-obligations-proving-v1.json',dict(stage='proving',required=[dict(name=n,statement_hash=h,state='contract-source-stabilized-body-pending') for n,h in freeze['headers'].items()],first_ready_leaf='meanPredict_zero_cumulativeLoss',finite_terminal='guessing_vs_mean_unbounded',chapter_total=None,source_package_accepted=False,goal_complete=False))
write('30_lower_worker-plan-v1.md','Single lower proof route fixed after distinct source stabilization. New first leaf unfolds actual source meanPredict/empiricalMean on the zero stream; only initial contribution1/4 survives in nonempty finite range, using actual sum_ite_eq\x27. Actual lower witness gives regret>=n/4 at positive square horizon; subtract produced exact mean loss yields n/4-1/4 gap. exists_nat_gt(max(4*C+1,(N:real))) produces n>N/positive n and strict threshold inequality, then actual lower closes public terminal. No desired stability/regret/loss gap premise inserted. Each new theorem header must match native-v2 fingerprint and each attempt/compiler failure retained. Retained interval/gradient/regularity/tuned/lower proof bodies and2wholecanaries unchanged. Fresh named-public/root/Tests/21axes/12guards/fullsite/body/final source gates remain pending; not accepted source/chapter/book.')
print('Distinct source contract bound; stabilized->proving; first new ready zero-prefix finite sum leaf.')
