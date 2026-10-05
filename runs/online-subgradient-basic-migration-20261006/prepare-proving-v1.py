"""Bind the distinct closed/proper contract verdict before retained-body revalidation."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-BASIC-MIGRATION-20261006'
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
for row in load(run/'contract-source-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256'],row['path']
for p,h in reviewed.items():assert sha(p)==h,p
assert {n.rsplit('.',1)[-1] for n in r['target_verdicts']}==set(freeze['headers'])
for p,h in dict(freeze['module'],**freeze['canary'],**freeze['root_Tests']).items():assert sha(p)==h,p
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),verdict=r['verdict'],report_sha256=r['report_sha256'],required_reader_corrections=r.get('required_reader_corrections',[]),retained_proofs=2,retained_definitions=1,new_proofs=0,body_accepted=False,source_terminal_accepted=False))
for event in ['stabilized','proving']:
 gate(event+'-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=freeze['headers'],source_contract_receipt=str(run/'source-contract-receipt-v1.json'),route='single lower retained-body revalidation',first_ready_leaf='theorem_2_21',terminal='Two independent subgradient domain/convexity leaves sharing full support definition, no mutual theorem value edges',allowed_edits='leading ordinary ignored scope comment and selected reader only after distinct BODY review;2headers/all math tokens/1complete definition/whole3canaryproofs/rootTests fixed',retained_proofs=2,retained_definitions=1,new_proofs=0,source_terminal_accepted=False,chapter_complete=False,goal_complete=False)))
ob=load(run/'proof-obligations-v1.json');ob['stage']='proving'
for row in ob['required']:row['state']='source-stabilized-fresh-body-gates-pending'
write('proof-obligations-proving-v1.json',ob)
write('30_lower_worker-body-audit-v1.md','Actual finite global witness plus the supporting inequality rules out top at the supported point; source properness excludes bottom, yielding finite source domain. This actual theorem drops source convexity and exactly yields dom subdifferential subset domain/outside emptiness by universal witness unpacking. Theorem2.21 chooses a support at the convex combination, evaluates both endpoints, applies nonnegative weights including zero, and cancels weighted inner displacements using a+b=1. Actual globally REAL function and global ambient supports; existence is the legitimate printed hypothesis, desired convexity is produced. Generic complete definition accepts all EReal functions whereas original Definition2.20 explicitly proper; bottom and identicallytop would have all supports, so properness is not silently discarded. Arbitrary real inner product generalizes source finite Euclidean, ambient E nonempty via zero; V can be empty. Two independent retained proofs/one complete definition/no new mathematics. Whole3canaries quadratic global2x support, actual squareconvexity, genuine proper interval indicator no support at2.6namedaxes2nativeguards/3nodes320directreferences. Source interior existence and relative-interior footnote/T2.22/T2.23 remain mandatory separate.')
names=load(run/'public-named-declarations-v1.json')['axiom_probe'];assert len(names)==len(set(names))==6
write('leaves/public-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineSubgradientBasicCanary\n\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
print('Distinct subgradient contract bound;2retained proofs/1complete definition/whole3canaries/6axes prepared.')
