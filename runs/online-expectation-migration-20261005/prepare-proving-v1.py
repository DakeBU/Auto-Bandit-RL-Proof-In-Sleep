"""Enter bounded retained-body replay after the distinct contract verdict."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
run=Path(__file__).parent;task='ONLINE-EXPECTATION-MIGRATION-20261005'
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
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),verdict=r['verdict'],report_sha256=r['report_sha256'],required_reader_corrections=r.get('required_reader_corrections',[]),retained_proofs=7,retained_definitions=3,new_proofs=0,body_accepted=False))
snapshots=[]
for p in list(freeze['module'])+['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:
 dest=run/'leaves'/('pre-integration-'+p.replace('/','--')+'.txt');assert not dest.exists();dest.write_bytes(Path(p).read_bytes())
 snapshots.append(dict(path=p,snapshot=dest.as_posix(),raw_sha256=sha(dest),authorized_delta='leading dependency qualification comment only' if p.endswith('.lean') else 'only online-expectation reader subtree'))
write('historical-raw-supersession-v1.json',dict(rows=snapshots,previous_accepted_packages_immutable=True))
for event in ['stabilized','proving']:
 gate(event+'-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=freeze['headers'],source_contract_receipt=str(run/'source-contract-receipt-v1.json'),route='single lower retained-body revalidation',first_ready_leaf='positiveIntegral_coe',terminal_dependency='signedExpectation_coe_integrable + infinite-positive branch',allowed_edits='leading qualification comment/selected online-expectation reader subtree; all10headers/definitions/proof tokens/canary bytes fixed',retained_proofs=7,retained_definitions=3,new_proofs=0,chapter_complete=False,goal_complete=False)))
ob=load(run/'proof-obligations-v1.json');ob['stage']='proving'
for row in ob['required']:row['state']='source-stabilized-fresh-body-gates-pending'
write('proof-obligations-proving-v1.json',ob)
write('30_lower_worker-body-audit-v1.md','Retained definition semantics: positive/negative total ENNReal lintegrals, EReal embedded difference. Coercion identities by actual toENNReal rules. Positive-finite uses Integrable.pos_part and pinned a.e.-measurable/nonnegative lintegral finiteness iff; negative-finite applies real negation. Finite signed compatibility embeds two proved finite ENNReal values, uses EReal coefficient subtraction and pinned actual positive-minus-negative Bochner integral identity. A.e. nonnegative proves negative integrand a.e.zero then exact lintegral zero; positive-infinite result rewrites actual positive infinity and invokes EReal.top_sub only under negative finite. No arbitrary nonintegrable integral-zero or both-infinite shortcut, no source loss-integrability assumption. Seven retained bodies/three unchanged definitions/zero new proof code; current scoped10node317edge readiness only. Public replay/18names/10guards/body and integration gates pending.')
public=['BanditRL.OnlineConvex.'+n for n in freeze['headers']]
text=Path('Tests/OnlineExpectationCanary.lean').read_text(encoding='utf-8');namespace=re.search(r'(?m)^namespace\s+(\S+)',text).group(1)
canary=[namespace+'.'+n for n in re.findall(r'(?m)^(?:theorem|def)\s+(\S+)',text)]
assert len(canary)==8;names=public+canary;assert len(set(names))==18
write('leaves/public-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineExpectationCanary\n\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
write('public-named-declarations-v1.json',dict(axiom_probe=names,public_proofs=7,public_definitions=3,canary_proofs=6,canary_definitions=2,new_proofs=0,canary_boundary='twoAtoms mass2; count infinite mass, not probability-parent canaries'))
print('Distinct contract/originals bound; retained signed integral proving and18public names prepared, body acceptance pending.')
