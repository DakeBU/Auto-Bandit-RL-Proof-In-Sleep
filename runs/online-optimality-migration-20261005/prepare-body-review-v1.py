"""Bind four actual retained proof bodies/canary replay for a separate source-body verdict."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-OPTIMALITY-MIGRATION-20261005'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
labels=['focused-v1-01','public-body-v1-01','public-canary-v1-01','public-axioms-v1-01','verify-public-fences-v1-01']
for label in labels:assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v1.json');module=Path('BanditRLProof/OnlineConvexOptimality.lean')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(module.read_text(encoding='utf-8'))==tokens((run/'original-OnlineConvexOptimality.lean.txt').read_text(encoding='utf-8'))
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
names=load(run/'public-named-declarations-v1.json')['axiom_probe'];assert len(matches)==13 and {n for n,a in matches}==set(names)
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
write('public-actual-bindings-v1.json',dict(status='freshly-elaborated-retained-body-candidate',public_module={module.as_posix():sha(module)},canary=freeze['canary'],headers=freeze['headers'],
 axioms=axioms,named_axiom_count=13,native_guards=4,actual_passed_gates=labels,retained_proofs=4,new_proofs=0,new_registry_nodes=0,
 canary_definitions=1,canary_proofs=8,body_review='pending',root_Tests_harness='pending',reader_site_PR='pending',chapter_complete=False,goal_complete=False))
gate('retained-body-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','lower','--kind','build','--status','compiled','--run-id',run.name,
 '--attempt-id','OPTIMALITY-RETAINED-BODIES-V1','--lean',module.as_posix(),'--statement-hash',freeze['headers']['theorem_2_8'],
 '--reused-declaration','BanditRL.OnlineConvex.theorem_2_8','--verifier-evidence',str(run/'public-body-v1-01.log'),'--progress-class','retrieval-reuse',
 '--notes','Actual4retainedbody module/byte-unchanged meaningful canary/13namedaxioms/4nativeguards passed. No newproofcode; distinctbody/package review pending.')
write('public-body-review-packet-v1.md','''Required distinct BODY review GPT-6 Astra / medium. Independently hash public-body-inputs-v1.json rows and resolve original source92rawrows via prior-contract-binding-v1/historicalsnapshot. Four retained actualproofbodies, unchanged4nativeheaders/allcodetokens/wholecanarybytes, freshfocused/directpublicmodule/canary,13namedstandard3-or-noneaxioms/4nativeguards. Read actual proofterms, sourcev10p11PDF23 and neutraldecoder: minOnreal necessity localizedminimum/genuinegradientderivative/convexsegmentpositivetangent, sufficiency source-reviewed supportingbound; finitebridge exactboth-infinity exclusions/coeorder onV only; source terminal openU givesambientderivative then twoiffcomposition; interioractualFermat withretainedhd and ambientinterior, zero sufficiency fullcriterion. No desired criterion/gradient vector asoracle premise. Source neighborhoodconvexity weakenedtoV => strongerterminal, not equivalentpremises; noConvexU/no globalnoBottom/finiteoutsideU. CanonicalF embeddingfiniteU localderivative legitimate; IsMinOn notmembership. ActualFermatfallback cannotremovehd.

Publicactualcanary builds finite/derivative/sourceConvexOnUrestriction, nonzero-gradient boundaryminimum1 withsmaller0.5outsideV/larger2inside; quadratic actualderivativegrad0/nonconstantvalues0vs1/min onopen nonclosedV. Nozero-gradientboundarygeneralization/nonconvexsufficiency/existence/uniqueness/closedness/boundedness. Fresh scopedcompiled4node510directedgeproof graph/valuepairs isready actualboundary, notfull/canaryexport. Twohelpers notprintedtheorems; interiorzero unnumberedmandatorysource. Existingreader5requiredcorrections stillpending, separatefrommathrepairs. Root/Tests/fullharness/registry/readers/site/contributor/raw/package/PR pending. Whole Goalactive/Chapter2null/incomplete/legacy18beforepackage. WriteONLYpublic-body-review-v1.md/public-body-receipt-v1.json withactor.task=/root/source_reviewer, actualfour/sevenslots/canary/verdict, mathematical_repairs/reader corrections separate, reviewed_files/reportSHA. Noinputedits/human/external/runtimeattestation.''')
paths={row['path'] for row in load(run/'contract-source-inputs-v1.json')['rows']}
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
paths.add('.lake/packages/mathlib/Mathlib/Order/Filter/Extr.lean')
write('public-body-inputs-v1.json',dict(scope='four actual retained optimality bodies/unchanged nondegenerate canary/13namedaxiom results',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Fourretainedbody/canary/13namedaxiom/4guard proofevidence frozen; distinctBODY review pending.')
