"""Bind distinct source contract, preserve exact originals and enter bounded proving."""
from pathlib import Path
import json,hashlib,subprocess,sys,re
run=Path(__file__).parent;task='ONLINE-OPTIMALITY-MIGRATION-20261005'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
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
for row in load(run/'contract-source-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
for p,h in reviewed.items():assert sha(p)==h,p
assert {n.rsplit('.',1)[-1] for n in r['target_verdicts']}==set(freeze['headers'])
for p,h in dict(freeze['module'],**freeze['canary']).items():assert sha(p)==h,p
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),verdict=r['verdict'],report_sha256=r['report_sha256'],
 required_reader_corrections=r.get('required_reader_corrections',[]),retained_proofs=4,new_proofs=0,body_accepted=False))
snapshots=[]
for p in list(freeze['module'])+['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:
 dest=run/'leaves'/('pre-integration-'+p.replace('/','--')+'.txt');assert not dest.exists();dest.write_bytes(Path(p).read_bytes())
 snapshots.append(dict(path=p,snapshot=dest.as_posix(),raw_sha256=sha(dest),authorized_delta='leading source comment only' if p.endswith('.lean') else 'only online-optimality reader subtree'))
write('historical-raw-supersession-v1.json',dict(rows=snapshots,previous_accepted_packages_immutable=True))
for event in ['stabilized','proving']:
 gate(event+'-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,
  frozen_headers=freeze['headers'],source_contract_receipt=str(run/'source-contract-receipt-v1.json'),route='single lower retained body revalidation',
  first_ready_leaf='minOn_real_iff_gradient',terminals=['theorem_2_8','interior_min_iff_gradient_zero'],
  allowed_edits='leading source comment/selected online-optimality reader subtree; all4headers/proof tokens/canary bytes fixed',retained_proofs=4,new_proofs=0,chapter_complete=False,goal_complete=False)))
ob=load(run/'proof-obligations-v1.json');ob['stage']='proving'
for row in ob['required']:row['state']='source-stabilized-fresh-body-gates-pending'
write('proof-obligations-proving-v1.json',ob)
write('30_lower_worker-body-audit-v1.md','Four unchanged bodies inspected: real criterion necessity localizes actual minimum and evaluates genuine gradient derivative on feasible positive tangent from convex segment; sufficiency uses accepted convex supporting bound, not assumed criterion. Finite bridge compares candidate/comparator finite EReal embeddings under hfin onV only. theorem_2_8 gets actual ambient derivative via arbitrary openU and composes both helper iffs; explicit hV/hne remain despite redundant proof use. Interior necessity converts finite minimum to local minimum by ambient interior and uses actual Fermat/fderiv-zero/gradient Riesz; hd retained ensures actual derivative semantics, no fallback-zero source shortcut. Sufficiency invokes full feasible-direction criterion with gradientzero. Actual current graph4nodes510edges, source-stabilized only; public replay/13namedaxioms/4guards/body review and integration pending. Four retained proofs/zero newproofs.')
public=['BanditRL.OnlineConvex.'+n for n in freeze['headers']]
text=Path('Tests/OnlineConvexOptimalityCanary.lean').read_text(encoding='utf-8');namespace=re.search(r'(?m)^namespace\s+(\S+)',text).group(1)
canary=[namespace+'.'+n for n in re.findall(r'(?m)^(?:theorem|def)\s+(\S+)',text)]
assert len(canary)==9;names=public+canary;assert len(set(names))==13
write('leaves/public-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineConvexOptimalityCanary\n\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
write('public-named-declarations-v1.json',dict(axiom_probe=names,public_proofs=4,canary_proofs=8,canary_definitions=1,new_proofs=0,preceding_imported_loss_instance='Previously accepted Tests.OnlineConvexFirstOrder loss reused; own named endpoints audited here.'))
print('Distinct contract/originals bound;4retainedproof proving and13public names prepared, body acceptance pending.')
