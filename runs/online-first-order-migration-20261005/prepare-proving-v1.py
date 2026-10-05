"""Verify distinct contract bindings and fix the retained-body verification route."""
from pathlib import Path
import json,hashlib,subprocess,sys,re
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-FIRST-ORDER-MIGRATION-20261005'
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
    p=run/n;assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
r=load(run/'source-contract-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r['mathematical_repairs'] and sha(r['report'])==r['report_sha256']
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
for row in load(run/'contract-source-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
for p,h in reviewed.items():assert sha(p)==h,p
assert set(n.rsplit('.',1)[-1] for n in r['target_verdicts'])==set(freeze['headers'])
for p,h in dict(freeze['module'],**freeze['canary']).items():assert sha(p)==h,p
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),verdict=r['verdict'],report_sha256=r['report_sha256'],
    required_reader_corrections=r.get('required_reader_corrections',[]),retained_proofs=3,new_proofs=0,body_accepted=False))
for event in ['stabilized','proving']:
    gate(event+'-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,
        frozen_headers=freeze['headers'],source_contract_receipt=str(run/'source-contract-receipt-v1.json'),route='single lower retained body revalidation',
        first_ready_leaf='finitePart_eventually',terminal='theorem_2_7',allowed_edits='source qualification comment and only online-first-order reader subtree; proof tokens/headers/canary bytes fixed',
        retained_proofs=3,new_proofs=0,chapter_complete=False,goal_complete=False)))
ob=load(run/'proof-obligations-v1.json');ob['stage']='proving'
for row in ob['required']:row['state']='source-stabilized-fresh-body-gates-pending'
write('proof-obligations-proving-v1.json',ob)
write('30_lower_worker-body-audit-v1.md','Three unchanged actual bodies inspected. Neighborhood equality uses open interior membership, interior_subset and coe_toReal with both infinity exclusions. Real supporting bound composes ConvexOn with the affine line x→y, proves its derivative y-x at zero and uses le_slope_of_hasDerivAt at zero/one plus the actual gradient derivative; no desired supporting inequality assumed. Printed terminal proves x finite from actual neighborhood identity; inside-domain y uses the accepted extended-convex/ConvexOn finite-part iff plus the real helper; outside-domain y is proved top and le_top closes it. Canonical real conversion is not substituted for f(y) globally. Three retained proofs/zero new proofs, actual current scoped graph416edges/source-stabilized; fresh public module/canary/named axioms/guards/body review and integrated gates pending.')
public=['BanditRL.OnlineConvex.'+n for n in freeze['headers']]
canary_path=Path('Tests/OnlineConvexFirstOrderCanary.lean');text=canary_path.read_text(encoding='utf-8')
namespace=re.search(r'(?m)^namespace\s+(\S+)',text).group(1)
canary=[namespace+'.'+n for n in re.findall(r'(?m)^(?:theorem|def)\s+(\S+)',text)]
assert len(canary)==9
names=public+canary;assert len(set(names))==12
write('leaves/public-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineConvexFirstOrderCanary\n\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
write('public-named-declarations-v1.json',dict(axiom_probe=names,public_proofs=3,canary_proofs=8,canary_definitions=1,anonymous_canary_instance=1,new_proofs=0))
print('Distinct contract bindings passed; stabilized/proving and12 named probes prepared; retained-body acceptance pending.')
