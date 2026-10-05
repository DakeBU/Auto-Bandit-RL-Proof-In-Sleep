"""Bind the distinct closed/proper contract verdict before retained-body revalidation."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-CLOSED-PROPER-MIGRATION-20261006'
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
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),verdict=r['verdict'],report_sha256=r['report_sha256'],required_reader_corrections=r.get('required_reader_corrections',[]),retained_proofs=3,retained_definitions=2,new_proofs=0,body_accepted=False,source_terminal_accepted=False))
for event in ['stabilized','proving']:
 gate(event+'-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=freeze['headers'],source_contract_receipt=str(run/'source-contract-receipt-v1.json'),route='single lower retained-body revalidation',first_ready_leaf='sourceClosed_iff_lowerSemicontinuous',terminal='Three independent closed/proper equivalences, no theorem-to-theorem value edges',allowed_edits='leading ordinary ignored scope comment and selected reader only after distinct review;3headers/all math tokens/2complete definitions/whole6canaryproofs/rootTests fixed',retained_proofs=3,retained_definitions=2,new_proofs=0,source_terminal_accepted=False,chapter_complete=False,goal_complete=False)))
ob=load(run/'proof-obligations-v1.json');ob['stage']='proving'
for row in ob['required']:row['state']='source-stabilized-fresh-body-gates-pending'
write('proof-obligations-proving-v1.json',ob)
write('30_lower_worker-body-audit-v1.md','Actual real-cut complements and EReal density derive bottom strict superlevel as real-cut union, with top empty and closed-preimage reverse, proving LSC equivalence on arbitrary topological domains including bottom losses. Canonical indicator exact cuts at nonnegative/negative real thresholds prove closed iff closed V, with r0 necessity. Genuine finite indicator point proves membership; member produces value0/nowherebottom for proper iff nonempty. SourceProper itself topology-free but actual properiff retains TopologicalSpace binder. Three independent retained leaves/no false theorem value edges. Whole6canaries bottom closed/LSC/improper, real interval nonconstant indicator closed/proper, empty improper.3retainedproofs2full defs/0newmathgain;11axes3guards/5nodes213directreferences, notfull/canarygraph. Reader/package/Chapter2/Book pending.')
names=load(run/'public-named-declarations-v1.json')['axiom_probe'];assert len(names)==len(set(names))==11
write('leaves/public-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineClosedProperCanary\n\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
print('Distinct closed/proper contract bound;3retained bodies/2definitions/whole6canaries/11namedaxes prepared.')
