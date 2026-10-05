"""Freeze fresh actual retained-body, full canary and named axiom evidence."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-EXPECTATION-MIGRATION-20261005'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as h:
  if isinstance(x,str):h.write(x.rstrip('\n')+'\n')
  else:json.dump(x,h,ensure_ascii=False,indent=2);h.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
labels=['focused-v1-01','public-body-v1-01','public-canary-v1-01','public-axioms-v1-01','verify-public-fences-v1-01']
for label in labels:assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v1.json');module=Path('BanditRLProof/OnlineExpectation.lean')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(module.read_text(encoding='utf-8'))==tokens((run/'original-OnlineExpectation.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(module,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
r=load(run/'source-contract-receipt-v1.json');assert sha(r['report'])==r['report_sha256']
snap={(row['path'],row['raw_sha256']):row['snapshot'] for row in load(run/'historical-raw-supersession-v1.json')['rows']}
oldrows=[]
for row in r['reviewed_files']:
 p,h=row['path'],row['sha256'];resolved=p if sha(p)==h else snap[(p,h)]
 assert sha(resolved)==h;oldrows.append(dict(path=p,sha256=h,resolved=resolved))
write('prior-contract-binding-v1.json',dict(status='passed',rows=oldrows,explicit_module_comment_supersession=True,original_receipt_immutable=True))
raw=(run/'public-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
names=load(run/'public-named-declarations-v1.json')['axiom_probe'];assert len(matches)==18 and {n for n,a in matches}==set(names)
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
write('public-actual-bindings-v1.json',dict(status='freshly-elaborated-retained-body-candidate',public_module={module.as_posix():sha(module)},canary=freeze['canary'],headers=freeze['headers'],axioms=axioms,named_axiom_count=18,native_guards=10,actual_passed_gates=labels,retained_proofs=7,retained_definitions=3,new_proofs=0,new_registry_nodes=0,canary_definitions=2,canary_proofs=6,body_review='pending',root_Tests_harness='pending',reader_site_PR='pending',parent_accepted=False,chapter_complete=False,goal_complete=False))
gate('retained-body-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','lower','--kind','build','--status','compiled','--run-id',run.name,'--attempt-id','EXPECTATION-RETAINED-BODIES-V1','--lean',module.as_posix(),'--statement-hash',freeze['headers']['signedExpectation_coe_integrable'],'--reused-declaration','BanditRL.OnlineConvex.signedExpectation_coe_integrable','--verifier-evidence',str(run/'public-body-v1-01.log'),'--progress-class','retrieval-reuse','--notes','Actual7retainedbodies/3definitions/byte-unchanged meaningful nonprobability canary/18namedaxioms/10nativeguards passed. No newproofcode; distinctbody/package review pending, not Jensen acceptance.')
write('public-body-review-packet-v1.md','''Required distinct BODY review GPT-6 Astra / medium. Hash public-body-inputs-v1.json rows and resolve all124 prior source receipt rows via prior-contract-binding-v1 and historical snapshots. Read sourcev10p11PDF23, neutral decoder, actual public definitions/seven retainedproofbodies, actual APIs and fresh module/focused/fullcanary/18namedaxioms/10nativeguards. All10nativeheaders/definition/proof tokens/canarybytes unchanged, leading dependency comment only. SourceTheorem2.9 is parent, not7printedhelpers or acceptance. Actual proof routes: coercion toENNReal; Integrable.pos_part + actual measurable nonnegative lintegral finiteness characterization; negate for negativepart; provedtwofiniteparts embedding + actual Bochner decomposition; a.e.nonnegative negativeintegrandzero; explicit negativefinite for EReal.top_sub infinitepositive. No desired integrability or expectation equality as oracle; no nonintegrable Bochner-zero or both-infinite shortcut.

Scope arbitrarymeasure/non-normalized/possiblyinfinite mass/functions no meas premise unless actualIntegrable suppliesa.e.strongmeas. Totaldefinitions/formalalgebra vs legitimate signedintegral interpretation separated; top-top=bottom is excluded from that meaning. Nonnegativehelper only AEcondition/no meas/integrability, allowspositive∞. Parent Jensen must separatelyproduce finite negativepart from sourceassumptions/affineminorant; parent/code historical status not accepted here.

CanaryactualtwoAtoms mass2 identityintegral2, notprobability expectation1; growing n+1 countmeasure finitepointvalues/nonconstant/positive∞/negative0/signedtop, notprobability Jensen case. Sixproofs/twodefs byteexact freshlycompiled. Scopedcompiled10node317directedges graph beforecomment withsamecodetokens, notfull/canaryexport. Sixreader corrections pending separatefinalphase. Old historical expectation acceptance/initial failedcanarysorryAx rejected retained, currentnamed18standard3-or-none only. Root/Tests/fullharness/registry/reader/site/contributor/raw/package/PR pending. WholeGoalACTIVE/Chapter2null/incomplete/legacy17beforepackage. WriteONLY public-body-review-v1.md/public-body-receipt-v1.json here, actor.task=/root/source_reviewer, all10/sevenslots/actualproofs/canary/verdict, mathematical_repairs vs required_reader_corrections, reviewed_files/reportpath/SHA. No inputs edits/human/external/runtime attestation.''')
paths={row['path'] for row in load(run/'contract-source-inputs-v1.json')['rows']}
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
paths.add('runs/online-jensen-20260914/expectation-acceptance-decision.md')
write('public-body-inputs-v1.json',dict(scope='seven retained expectation bodies/three definitions/nonprobability canary/18namedaxioms',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Actual7retainedbody/3definition/canary/18namedaxiom/10guard evidence frozen; distinctBODY review pending.')
