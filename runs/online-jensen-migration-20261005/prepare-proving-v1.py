"""Bind distinct source stabilization and prepare the exact retained Jensen bodies."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-JENSEN-MIGRATION-20261005'
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
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),verdict=r['verdict'],report_sha256=r['report_sha256'],required_reader_corrections=r.get('required_reader_corrections',[]),retained_proofs=2,retained_definitions=0,new_proofs=0,body_accepted=False,source_terminal_accepted=False))
snapshots=[]
for p in list(freeze['module'])+['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:
 dest=run/'leaves'/('pre-integration-'+p.replace('/','--')+'.txt');assert not dest.exists();dest.write_bytes(Path(p).read_bytes())
 snapshots.append(dict(path=p,snapshot=dest.as_posix(),raw_sha256=sha(dest),authorized_delta='leading source/scope qualification comment only' if p.endswith('.lean') else 'only online-jensen reader subtree'))
write('historical-raw-supersession-v1.json',dict(rows=snapshots,previous_accepted_packages_immutable=True))
for event in ['stabilized','proving']:
 gate(event+'-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=freeze['headers'],source_contract_receipt=str(run/'source-contract-receipt-v1.json'),route='single lower retained-body revalidation',first_ready_leaf='jensen_negativeIntegral_ne_top',terminal='theorem_2_9: exact source inequality allowing positive-infinite loss expectation',allowed_edits='leading source/scope qualification comment and selected online-jensen reader subtree; two headers/proof tokens/whole canary bytes fixed',retained_proofs=2,retained_definitions=0,new_proofs=0,source_terminal_accepted=False,chapter_complete=False,goal_complete=False)))
ob=load(run/'proof-obligations-v1.json');ob['stage']='proving'
for row in ob['required']:row['state']='source-stabilized-fresh-body-gates-pending'
write('proof-obligations-proving-v1.json',ob)
write('30_lower_worker-body-audit-v1.md','Actual negative-part producer obtains a nonempty-domain witness from probability AE membership, accepted global continuous real affine minorant, actual affine-composed input integrability and pointwise negative domination; real negativeIntegral compatibility supplies finiteness. No loss-integrability or supplied negative-finite premise. Terminal invokes producer; infinite positive part yields legitimate signed top. Otherwise measurable toReal Y has actual AE finite embedding from hbot/domain; finite part integrals produce integrable positive/negative maxima, their difference produces Integrable Y; actual integrable pair lies AE in original real epigraph. Accepted nonclosed barycenter and actual pair-integral/AE signed-real-integral compatibility yield source inequality, not closure-only membership. Actual finiteD realnormed MeasurableSpace/Borel scope; source finite Lebesgue-coordinate-mean interpretation explicitly contract-reviewed, no nonintegrable-zero/principal-value fallback. Whole original canary13proofs3defs2probinstances includes normalized finite nonconstant, genuine probability-geometric infinite loss, nonclosed lowerdim loss domain. Two retained production proofs/no productiondefs/newcode/nodes; planned20namedaxioms2guards and package gates pending. Actual scoped2nodes350directedges, not full/canary export; chapter/book Goal still incomplete.')
public=['BanditRL.OnlineConvex.'+n for n in freeze['headers']]
groups={
 'Tests.OnlineJensenInfinite':['law','X','atom','weighted','X_integrable','square_infinite','source_infinite_instance','instIsProbabilityMeasureLaw'],
 'Tests.OnlineJensenFinite':['law','integrable_atom_function','mean','square_expectation','source_finite_instance','instIsProbabilityMeasureLaw'],
 'Tests.OnlineJensenNonclosed':['measurable_ray','loss_measurable','source_nonclosed_instance','domain_is_nonclosed']}
canary=[ns+'.'+n for ns,names in groups.items() for n in names];names=public+canary
assert len(canary)==18 and len(set(names))==20
write('leaves/public-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineJensenCanary\n\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
write('public-named-declarations-v1.json',dict(axiom_probe=names,public_proofs=2,public_definitions=0,canary_proofs=13,canary_definitions=3,canary_probability_instances=2,new_proofs=0,generated_instance_names_status='must actually #check and audit before candidate',canary_boundary='Normalized finite nonconstant input/positive-infinite square expectation under actual geometric probability/nonclosed lower-dimensional loss domain; not counting-measure foundation test'))
print('Distinct source contract bound; two retained bodies and all20named declarations prepared, actual instance checks pending.')
