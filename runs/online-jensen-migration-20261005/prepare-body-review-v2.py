"""Freeze actual producer/terminal elaboration, three probability canaries and named axioms."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-JENSEN-MIGRATION-20261005'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))

def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')

def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
labels=['focused-v1-01','public-body-v1-01','public-canary-v1-01','public-axioms-v2-01','verify-public-fences-v1-01']
for label in labels:assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v1.json');module=Path('BanditRLProof/OnlineJensen.lean')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(module.read_text(encoding='utf-8'))==tokens((run/'original-OnlineJensen.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(module,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
r=load(run/'source-contract-receipt-v1.json');assert sha(r['report'])==r['report_sha256']
snap={(row['path'],row['raw_sha256']):row['snapshot'] for row in load(run/'historical-raw-supersession-v1.json')['rows']}
oldrows=[]
for row in r['reviewed_files']:
 p,h=row['path'],row['sha256'];resolved=p if sha(p)==h else snap[(p,h)];assert sha(resolved)==h
 oldrows.append(dict(path=p,sha256=h,resolved=resolved))
write('prior-contract-binding-v1.json',dict(status='passed',rows=oldrows,explicit_module_comment_supersession=True,original_receipt_immutable=True))
raw=(run/'public-axioms-v2-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
names=load(run/'public-named-declarations-v2.json')['axiom_probe'];assert len(matches)==20 and {n for n,a in matches}==set(names)
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
assert 'Tests.OnlineJensenInfinite.instIsProbabilityMeasureNatLaw' in axioms and 'Tests.OnlineJensenFinite.instIsProbabilityMeasureRealLaw' in axioms
write('public-actual-bindings-v1.json',dict(status='freshly-elaborated-retained-body-candidate',public_module={module.as_posix():sha(module)},canary=freeze['canary'],headers=freeze['headers'],axioms=axioms,named_axiom_count=20,native_guards=2,actual_passed_gates=labels,retained_proofs=2,retained_definitions=0,new_proofs=0,new_registry_nodes=0,canary_definitions=3,canary_proofs=13,canary_probability_instances=2,generated_instance_names_actually_checked=True,body_review='pending',root_Tests_harness='pending',reader_site_PR='pending',source_terminal_accepted=False,chapter_complete=False,goal_complete=False))
gate('retained-body-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','lower','--kind','build','--status','compiled','--run-id',run.name,'--attempt-id','JENSEN-RETAINED-BODIES-V1','--lean',module.as_posix(),'--statement-hash',freeze['headers']['theorem_2_9'],'--reused-declaration','BanditRL.OnlineConvex.theorem_2_9','--verifier-evidence',str(run/'public-body-v1-01.log'),'--progress-class','retrieval-reuse','--notes','Actual retained negative-finite producer/source Jensen bodies and unchanged three probability canaries13proofs3defs2probinstances/20namedaxioms/2guards passed. No new proof code; distinct BODY and package acceptance pending, Chapter2/Book incomplete.')
write('public-body-review-packet-v1.md','''Required distinct BODY review GPT-6 Astra/medium. Independently hash ALL public-body-inputs-v1.json rows and resolve114 prior contract rows through prior-contract-binding-v1/exact raw snapshots. Two actual headers/contexts/proof tokens and entire original canary bytes unchanged, leading source/scope comment only. Source v10 Theorem2.9 p11/PDF23, neutral reconstruction and actual scoped2node350edge direct type/value graph/pinned APIs. One printed source theorem plus required negative-part producer, not two printed results.

Seek hidden consumers: negative-finite is genuinely produced using actual domain witness from probability AE membership, accepted global affine minorant, actual Integrable affine(X) and pointwise domination/real-negative-integral compatibility, not assumed. No loss Integrable, supplied negative-finite or desired affine bound. Source hfm/hXm stay in its actual type even if unused in body. Terminal invokes producer. Positive-infinite branch uses signed top with finite negative part, giving le_top only; not a finite mean-loss/domain claim. Finite-positive branch produces measurable Y=toReal(f∘X), genuine AE embedding from sampled finiteness/hbot, actual integrable positive/negative maxima using finite lintegrals, actual Integrable Y as difference, actual integrable joint (X,Y) and original convex real-epigraph AE membership. Accepted nonclosed finiteD barycenter, integral_pair and signed real compatibility/AE equality give exactly f(mean)≤signedExpectation. No desired epigraph barycenter/Integrable Y/Jensen oracle or closure substitute.

Contract finite-mean interpretation explicitly accepted: ordinary finite Lebesgue coordinate expectations ↔ finiteD genuine Bochner Integrable via checked Pi/PiLp. No principal-value/total nonintegrable-zero fallback. Actual finiteD realnormed measurable/Borel E, no supplied CompleteSpace/innerproduct, Euclidean generality explicit. Probability mass1, global no-bottom, measurable convex loss, measurable/Integrable X, AE domain; no closed/lsc/full-dimensional-domain/finite-support/lossdiff/lossIntegrable assumption. Actual total signed subtraction is mathematical expectation here because finite negative part proved; both-infinite regime unreachable, positive∞ allowed, no finite regret/strict inequality guarantee.

Whole bytefixed canary13proofs3defs2probabilityinstances. Finite normalized halfdirac1/3 nonconstant mean2/square5; normalized geometric p3/4, input2^n integrable, square loss finite each sample yet positive integral∞; nonclosed lowerdim coordinate/topoutside domain under actual probability law, measurable loss/AE domain/source theorem. Actual generated probability instance names #checked and axiom-audited, ALL20names2public+13proof+3defs+2instances standard3-or-none/no sorryAx. Two native guards not compilation. Fresh focused/public body/whole canary/axes/guards passed, but root/Tests/full/contributor/site/registry/finalreader/PR pending. Seven contract reader fixes remain pending; semantic/body fixes separately identify, no input edits. API v1 wrong qualified integral_pair fail preserved/v2 lookup fixed, no mathematical repair. Global reference-index refresh deliberately not run; scoped environment fresh. Exact stacked OPENdraft1622b4586db..., legacy14beforepackage/Chapter2null/incomplete/wholeGoalACTIVE. Write ONLY public-body-review-v1.md/public-body-receipt-v1.json with actor.task=/root/source_reviewer, two targetverdicts/seven slots/actual producers/canaries/finite-mean decision/readercorrections versus mathematicalrepairs/ALL reviewed files/reportSHA. No human/external/runtime attestation.''')
paths={row['path'] for row in load(run/'contract-source-inputs-v1.json')['rows']}
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
write('public-body-inputs-v1.json',dict(scope='two retained Jensen/negative-finite producer bodies, whole three probability canaries/20 named axioms',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Actual two producer/terminal bodies, whole probability canary20axes2guards frozen; distinct BODY pending.')
