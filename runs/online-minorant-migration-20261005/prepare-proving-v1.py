"""Bind the distinct contract and replay the exact retained minorant bodies."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
run=Path(__file__).parent;task='ONLINE-MINORANT-MIGRATION-20261005'
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
for row in load(run/'contract-source-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
for p,h in reviewed.items():assert sha(p)==h,p
assert {n.rsplit('.',1)[-1] for n in r['target_verdicts']}==set(freeze['headers'])
for p,h in dict(freeze['module'],**freeze['canary']).items():assert sha(p)==h,p
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),verdict=r['verdict'],report_sha256=r['report_sha256'],required_reader_corrections=r.get('required_reader_corrections',[]),retained_proofs=4,retained_definitions=0,new_proofs=0,body_accepted=False,parent_accepted=False))
snapshots=[]
for p in list(freeze['module'])+['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:
 dest=run/'leaves'/('pre-integration-'+p.replace('/','--')+'.txt');assert not dest.exists();dest.write_bytes(Path(p).read_bytes())
 snapshots.append(dict(path=p,snapshot=dest.as_posix(),raw_sha256=sha(dest),authorized_delta='leading dependency qualification comment only' if p.endswith('.lean') else 'only online-minorant reader subtree'))
write('historical-raw-supersession-v1.json',dict(rows=snapshots,previous_accepted_packages_immutable=True))
for event in ['stabilized','proving']:
 gate(event+'-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=freeze['headers'],source_contract_receipt=str(run/'source-contract-receipt-v1.json'),route='single lower retained-body revalidation',first_ready_leaf='affine_support_of_finite_neighborhood',terminal_dependency='convex_affine_minorant: global continuous real affine bound without ambient-interior/closedness premise',allowed_edits='leading qualification comment/selected online-minorant reader subtree; all4headers/proof tokens/canary bytes fixed',retained_proofs=4,retained_definitions=0,new_proofs=0,parent_accepted=False,chapter_complete=False,goal_complete=False)))
ob=load(run/'proof-obligations-v1.json');ob['stage']='proving'
for row in ob['required']:row['state']='source-stabilized-fresh-body-gates-pending'
write('proof-obligations-proving-v1.json',ob)
write('30_lower_worker-body-audit-v1.md','Finite-neighbourhood support genuinely produces finite-point graph boundary through the auxiliary vertical identity local-min contradiction, nonzero support L on E x R, decomposition A/c and c<=0, auxiliary linear localmax→c!=0→c<0, global noBottom, then legal division/affine touching support. No differentiability of f assumed. Domain-interior helper produces neighbourhood finiteness from actual hbot/domain; next helper drops contact only. General minorant produces convex domain/intrinsic-interior affine-span restriction/translated direction-space ambient interior, invokes interior helper, actually extends the linear map to E with finite-dimensional continuity and corrects the intercept, yielding a global bound including top outside. No ambient-interior/lsc/closedness/measurability/negative-coefficient/minorant oracle enters general terminal. Output slopes mayzero, no chosen boundary contact promised. Four actual finiteDim realnormed scopes have no supplied Borel/probability/CompleteSpace classes despite historical stale contract prose. Four retained production proofs/no definitions/newcode/nodes. Bytefixed coordinate-loss/topoutside nonclosed lowerdimray canary6proofs1def,11names/4guards/fresh body and package gates pending. Scoped4node896directedges readiness, not full/canary export; parentJensennegativeproducer notaccepted.')
public=['BanditRL.OnlineConvex.'+n for n in freeze['headers']]
text=Path('Tests/OnlineConvexMinorantCanary.lean').read_text(encoding='utf-8');namespace=re.search(r'(?m)^namespace\s+(\S+)',text).group(1)
canary=[namespace+'.'+n for n in re.findall(r'(?m)^(?:theorem|def)\s+(\S+)',text)]
assert len(canary)==7;names=public+canary;assert len(set(names))==11
write('leaves/public-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineConvexMinorantCanary\n\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
write('public-named-declarations-v1.json',dict(axiom_probe=names,public_proofs=4,public_definitions=0,canary_proofs=6,canary_definitions=1,new_proofs=0,canary_boundary='Coordinate on nonclosed lower-dimensional ray/topoutside: actual values1/3/top, global minorant; no probability/Jensen expectation claim'))
print('Distinct contract/originals bound; exact four minorant bodies/11public names prepared, acceptance pending.')
