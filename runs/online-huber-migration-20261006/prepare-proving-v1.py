"""Bind the distinct Huber contract verdict before retained-body revalidation."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-HUBER-MIGRATION-20261006'
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
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),verdict=r['verdict'],report_sha256=r['report_sha256'],required_reader_corrections=r.get('required_reader_corrections',[]),retained_proofs=19,retained_definitions=3,new_proofs=0,body_accepted=False,source_terminal_accepted=False))
for event in ['stabilized','proving']:
 gate(event+'-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=freeze['headers'],source_contract_receipt=str(run/'source-contract-receipt-v1.json'),route='single lower retained-body revalidation',first_ready_leaf='hasDerivAt_ite_le',terminal='huber_average_eventually: one-sided actual average regret eventually < every positive epsilon for fixed comparator, separate known-horizon constant-step runs',allowed_edits='leading ordinary ignored scope comment and selected online-huber reader subtree only after review;19headers/all math tokens/3full definitions/wholecanary/root/Tests fixed',retained_proofs=19,retained_definitions=3,new_proofs=0,source_terminal_accepted=False,chapter_complete=False,goal_complete=False)))
ob=load(run/'proof-obligations-v1.json');ob['stage']='proving'
for row in ob['required']:row['state']='source-stabilized-fresh-body-gates-pending'
write('proof-obligations-proving-v1.json',ob)
write('30_lower_worker-body-audit-v1.md','Actual retained scalar gluing uses matching values/derivatives and produces both seam derivatives including delta0; exact clamp/sign/global convexity/derivative bound follow. Actual linear inner-product chain rule produces vector gradient, affine-pullback convexity and norm bound. Genuine full-space Domain/projection identity and produced global RegularLoss feed the same causal shared OGD fixed-positive-step theorem, preserving negative terminal residual for all T>=0. Positive known horizon eta_T=1/sqrtT and actual square-root algebra yield average upper envelope; numerical envelope Tendsto0 combines with actual bound to prove the one-sided actual eventual-average<epsilon terminal for each fixed comparator. No regret/single-step/regularity oracle, bounded predictor domain, label bound, future-loss algorithm existence, literal actual-average Tendsto0 or anytime trajectory. Whole unchanged14canaries include both seams/delta0/nonzero featuregradient6/true full-space update/sharp residual/T4average5/4/eventual<1/10.19retainedproofs3defs0new;36namedaxes19guards/scoped22nodes2954directreferences pending fresh body gate, no full/canary graph claim. Reader corrections remain separately pending; Chapter2/Book incomplete.')
names=load(run/'public-named-declarations-v1.json')['axiom_probe'];assert len(names)==len(set(names))==36
write('leaves/public-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineHuberCanary\n\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
print('Distinct Huber contract bound; actual19retained bodies/3definitions/whole14canaries/36namedaxes prepared.')
