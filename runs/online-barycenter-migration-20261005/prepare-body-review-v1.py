"""Freeze actual replay, probability canary and all14 named axiom evidence."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-BARYCENTER-MIGRATION-20261005'
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
freeze=load(run/'draft-freeze-v1.json');module=Path('BanditRLProof/OnlineConvexBarycenter.lean')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(module.read_text(encoding='utf-8'))==tokens((run/'original-OnlineConvexBarycenter.lean.txt').read_text(encoding='utf-8'))
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
names=load(run/'public-named-declarations-v1.json')['axiom_probe'];assert len(matches)==14 and {n for n,a in matches}==set(names)
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
write('public-actual-bindings-v1.json',dict(status='freshly-elaborated-retained-body-candidate',public_module={module.as_posix():sha(module)},canary=freeze['canary'],headers=freeze['headers'],axioms=axioms,named_axiom_count=14,native_guards=3,actual_passed_gates=labels,retained_proofs=3,retained_definitions=0,new_proofs=0,new_registry_nodes=0,canary_definitions=3,canary_proofs=7,canary_probability_instances=1,body_review='pending',root_Tests_harness='pending',reader_site_PR='pending',parent_accepted=False,chapter_complete=False,goal_complete=False))
gate('retained-body-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','lower','--kind','build','--status','compiled','--run-id',run.name,'--attempt-id','BARYCENTER-RETAINED-BODIES-V1','--lean',module.as_posix(),'--statement-hash',freeze['headers']['integral_mem_convex_finiteDimensional'],'--reused-declaration','BanditRL.OnlineConvex.integral_mem_convex_finiteDimensional','--verifier-evidence',str(run/'public-body-v1-01.log'),'--progress-class','retrieval-reuse','--notes','Actual3retainedbodies/nonclosed probability canary/14namedaxioms including law_probability/3nativeguards passed. Zero newproofcode; distinctbody/package review pending, no Jensen acceptance.')
write('public-body-review-packet-v1.md','''Required distinct BODY review GPT-6 Astra / medium. Hash public-body-inputs-v1.json rows and resolve prior source receipt via prior-contract-binding-v1/historical snapshots. Read frozen v10 p11/PDF23 parent, neutral decoder, actual3publicproofbodies/scopedcontexts/actualtypes, pinned APIs, fresh module/focused/fullcanary/14namedaxioms INCLUDING law_probability/3nativeguards. All3nativeheaders/proof tokens/canary bytes unchanged, leading dependency comment only. SourceTheorem2.9 is parent, not3printedhelpers/acceptance.

Verify produced equal-support mean from actualintegrability/AEorder/probabilityconstant; separator from nonempty AMBIENTinterior HB or properaffinespan/nonzeroannihilator; genuine stronginduction finrank actualsetmembership via closedclosure startingpoint, nonzero support, AEequality, centered properkernel AEsubtype representative, actualisometry integrability/zero kernelintegral, affinepreimageconvexity/AE membership, strict kernelrank descent/recursion. Do not accept closedness/closure-only target, fullinterior restriction or assumed desired one-step/geometric/integrability/zero-mean/descent consumer. Complete normed equality versus finite-dimensional geometric and finite-dimensional Borel-context barycenter exactly distinguished, including zero dimension/default totalintegral boundaries.

Actualprobability halfdirac1+halfdirac3, vector(x)=(x,0), lowerdimensional nonclosed ray, actualmean(2,0) in ray, nonconstant endpoints;3defs/7proofs/1probabilityinstance bytefixed. This is meaningful barycentercanary, not sourceJensen performancecanary. Scoped3node544directedges only/not full/canarygraph. Separate reader correction finalphase/root/Tests/fullharness/registry/site/browser/contributor/raw/package/PR pending. WholeGoalACTIVE/Chapter2null/incomplete/legacy16beforepackage. Write ONLY public-body-review-v1.md/public-body-receipt-v1.json here; actor.task=/root/source_reviewer, three target/sevenslots/actualbodies/canary/verdict, mathematical_repairs separate required_reader_corrections, reviewed_files/reportpath/SHA. No input edits/human/external/runtime attestation.''')
paths={row['path'] for row in load(run/'contract-source-inputs-v1.json')['rows']}
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
write('public-body-inputs-v1.json',dict(scope='three retained barycenter/support bodies/probability nonclosed canary/14namedaxioms',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Actual3retainedbody/canary/14namedaxiom/3guard evidence frozen; distinctBODY review pending.')
