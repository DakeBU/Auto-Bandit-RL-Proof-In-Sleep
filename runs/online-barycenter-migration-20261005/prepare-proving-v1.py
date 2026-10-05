"""Bind distinct contract review and enter exact retained barycenter replay."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
run=Path(__file__).parent;task='ONLINE-BARYCENTER-MIGRATION-20261005'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('w',encoding='utf-8',newline='\n') as h:
  if isinstance(x,str):h.write(x.rstrip('\n')+'\n')
  else:json.dump(x,h,ensure_ascii=False,indent=2);h.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
r=load(run/'source-contract-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r.get('mathematical_repairs',r.get('required_mathematical_repairs',[])) and sha(r['report'])==r['report_sha256']
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
for row in load(run/'contract-source-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
for p,h in reviewed.items():assert sha(p)==h,p
assert {n.rsplit('.',1)[-1] for n in r['target_verdicts']}==set(freeze['headers'])
for p,h in dict(freeze['module'],**freeze['canary']).items():assert sha(p)==h,p
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),verdict=r['verdict'],report_sha256=r['report_sha256'],required_reader_corrections=r.get('required_reader_corrections',[]),retained_proofs=3,retained_definitions=0,new_proofs=0,body_accepted=False,parent_accepted=False))
snapshots=[]
for p in list(freeze['module'])+['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:
 dest=run/'leaves'/('pre-integration-'+p.replace('/','--')+'.txt');assert not dest.exists();dest.write_bytes(Path(p).read_bytes())
 snapshots.append(dict(path=p,snapshot=dest.as_posix(),raw_sha256=sha(dest),authorized_delta='leading dependency qualification comment only' if p.endswith('.lean') else 'only online-barycenter reader subtree'))
write('historical-raw-supersession-v1.json',dict(rows=snapshots,previous_accepted_packages_immutable=True))
for event in ['stabilized','proving']:
 gate(event+'-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=freeze['headers'],source_contract_receipt=str(run/'source-contract-receipt-v1.json'),route='single lower retained-body revalidation',first_ready_leaf='supporting_functional_ae_eq_mean',terminal_dependency='integral_mem_convex_finiteDimensional: actual-set membership by strict kernel-rank descent',allowed_edits='leading qualification comment/selected online-barycenter reader subtree; all3headers/proof tokens/canary bytes fixed',retained_proofs=3,retained_definitions=0,new_proofs=0,parent_accepted=False,chapter_complete=False,goal_complete=False)))
ob=load(run/'proof-obligations-v1.json');ob['stage']='proving'
for row in ob['required']:row['state']='source-stabilized-fresh-body-gates-pending'
write('proof-obligations-proving-v1.json',ob)
write('30_lower_worker-body-audit-v1.md','Three retained bodies: complete-normed support equality is produced by integrable linear composition/equal integrals/probability constant. Finite-dimensional separator uses nonempty ambient interior Hahn-Banach, or proper closed affine span/proper direction/nonzero annihilator when ambient interior is empty. Actual-set barycenter is genuine strong induction on finrank: pinned closed-convex integral proves only closure membership; supposing mean outside actual set produces nonzero supporting functional; actual AE order yields functional equality; centered subtype representative in proper kernel has integrability proved through isometry, its integral is proved zero, affine preimage preserves convexity and AE membership, strict kernel-rank descent permits recursion. No closedness assumption, closure-only terminal, oracle integrability/zero mean/dimension descent or presumed Jensen conclusion. Actual typeclasses differ across3headers and remain unchanged. Probability halfdirac1+halfdirac3/nonconstant lower-dimensional nonclosed ray canary unchanged. Three retained proofs/no definitions/zero new proof code/nodes; scoped3node544edge readiness only. Fresh replay/14names/3guards/body/root/Tests/fullharness/reader/site/PR pending.')
public=['BanditRL.OnlineConvex.'+n for n in freeze['headers']]
text=Path('Tests/OnlineConvexBarycenterCanary.lean').read_text(encoding='utf-8');namespace=re.search(r'(?m)^namespace\s+(\S+)',text).group(1)
canary=[namespace+'.'+n for n in re.findall(r'(?m)^(?:theorem|def|instance)\s+(\S+)',text)]
assert len(canary)==11 and namespace+'.law_probability' in canary
names=public+canary;assert len(set(names))==14
write('leaves/public-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineConvexBarycenterCanary\n\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
write('public-named-declarations-v1.json',dict(axiom_probe=names,public_proofs=3,public_definitions=0,canary_proofs=7,canary_definitions=3,canary_probability_instances=1,new_proofs=0,canary_boundary='probability mass1, vector(1,0) and (3,0), lower-dimensional nonclosed ray, actual mean(2,0) in ray'))
print('Distinct contract/originals bound; exact barycenter proving/14public names prepared, body acceptance pending.')
