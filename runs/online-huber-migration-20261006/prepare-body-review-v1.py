"""Freeze actual retained Huber elaboration and request a separate body review."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-HUBER-MIGRATION-20261006'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
labels=['focused-v1-01','public-body-v1-01','public-canary-v1-01','public-axioms-v1-01','verify-public-fences-v1-01']
for label in labels:assert load(run/(label+'-exit.json'))['exit_code']==0,label
assert re.search(r'Build completed successfully \(\d+ jobs\)',(run/'focused-v1-01.log').read_text(encoding='utf-8'))
freeze=load(run/'draft-freeze-v1.json');module=Path('BanditRLProof/OnlineHuber.lean')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(module.read_text(encoding='utf-8'))==tokens((run/'original-OnlineHuber.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(module,n).encode()).hexdigest()==h,n
for p,h in dict(freeze['canary'],**freeze['root_Tests']).items():assert sha(p)==h,p
r=load(run/'source-contract-receipt-v1.json');assert sha(r['report'])==r['report_sha256']
snap={(row['path'],row['raw_sha256']):row['snapshot'] for row in load(run/'historical-raw-supersession-v1.json')['rows']}
oldrows=[]
for row in r['reviewed_files']:
 p,h=row['path'],row['sha256'];resolved=p if sha(p)==h else snap[(p,h)];assert sha(resolved)==h,p
 oldrows.append(dict(path=p,sha256=h,resolved=resolved))
write('prior-contract-binding-v1.json',dict(status='passed',rows=oldrows,original_receipt_immutable=True))
raw=(run/'public-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
names=load(run/'public-named-declarations-v1.json')['axiom_probe'];assert len(matches)==len(names)==36 and {n for n,a in matches}==set(names)
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
write('public-actual-bindings-v1.json',dict(status='freshly-elaborated-retained-body-candidate',public_module={module.as_posix():sha(module)},canary=freeze['canary'],root_Tests=freeze['root_Tests'],headers=freeze['headers'],axioms=axioms,named_axiom_count=36,native_guards=19,actual_passed_gates=labels,retained_proofs=19,retained_definitions=3,new_proofs=0,new_registry_nodes=0,canary_proofs=14,canary_definitions=0,body_review='pending',root_Tests_harness='pending',reader_site_PR='pending',source_terminal_accepted=False,chapter_complete=False,goal_complete=False))
gate('retained-body-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','lower','--kind','build','--status','compiled','--run-id',run.name,'--attempt-id','HUBER-RETAINED-BODIES-V1','--lean',module.as_posix(),'--statement-hash',freeze['headers']['huber_average_eventually'],'--reused-declaration','BanditRL.OnlineHuber.huber_average_eventually','--verifier-evidence',str(run/'public-body-v1-01.log'),'--progress-class','retrieval-reuse','--notes','Actual retained19Huber scalar/vector/fullspace/causal OGD/one-sided average-terminal bodies,3full definitions/whole14canaries/36namedaxes/19guards passed. Zero new proof code/nodes; distinct BODY/package gates pending, Chapter2/Book incomplete.')
write('public-body-review-packet-v1.md','''Required DISTINCT BODY review, requested GPT-6 Astra/medium. Hash ALL public-body-inputs-v1.json rows and resolve ALL immutable prior contract rows using prior-contract-binding-v1.json/exact raw snapshots. Re-read source Example2.15 p15–16/PDF27–28,19actual public frozen headers/complete contexts/3full definitions and19complete actual proof bodies, neutral reconstruction, whole bytefixed14canaries, compiled22nodes2954directtype/value edges and pinned calculus/convex/limit/shared OGD APIs. ONE printed example,19retainedsupportproofs3definitions/0newproofs0newnodes. CONTRACT acceptance is separate from this actual BODY verdict; not automatic acceptance.

Search hidden consumers: generic matching-value/derivative gluing actually derives seam derivatives; Huber hasDerivAt and clamp/sign formulas derived for every residual/both seams/delta0; global convexity and derivative<=delta derived, not a supplied loss calculus/convexity oracle. Delta>=0 explicitly source-implicit and mathematically necessary; zero admitted, negative delta outside algorithm regularity. True linear innerSL affine composition derives ambient vector gradient/global convexity/norm<=delta*normz; no label/residual/predictor/diameter bound. Complete real Hilbert generality includes finite Euclidean source, actual class binders verified, not finiteD source equivalence claim. Actual fullSpace nonempty/closed/convex and selected projection identity; actual global RegularLoss is PRODUCED by huber_regular, so stronger historical API premise is discharged globally. Follow shared project/step/iterate/iterate_prefix/regret and actual proof value edges: same causal strict-prefix point, currentfeature availableprediction/currentlabel afterwards updatesnextpoint, no supplied desired stability/gradient/regret/point sequence or algorithmexistence reading all futurelosses.

Fixedeta>0/delta>=0/Z>=0/finiteprefix featurebound gives actual regret with preserved NEGATIVE finaldistance for allT>=0/x0/u. T0 cancellation,delta0/Z0 allowed. Generic step identity anyrealeta separate. Positive known horizon constant eta_T=1/sqrtT coefficient1 is valid instance of source proportional choice, not all coefficients/futureloss/comparator tuning. Actual square-root algebra/drop nonnegative residual gives actual average upper (norm(x0-u)^2+(deltaZ)^2)/(2sqrtT). Numeric envelope Tendsto0 permits arbitrary realdelta/Z by algebra; algorithm requiresdelta/Z>=0. Actual terminal for each fixedcomparator/globalfeaturebound/eachepsilon>0 is eventually actual average regret<epsilon, ONE-SIDED. It does NOT prove actualaverage Tendsto0/absolute differences vanishing or uniform cutoffoverunboundedcomparators. Separate known-horizon runfamily, not oneanytime eta_t trajectory/stronglyconvex Chapter4 guarantee. Mathematical reason: scalarz1/y0/x0=0/delta1/u1 producesactualaverage=-1/2, so literal convergence0 would be false; illustrative audit argument only, no new Lean counterexampleproof in this package.

Whole genuine14canaries0defs: generic upperjoin, lower/upperseams,delta0/interior/exterior, nonzero featuregradient6/bound6/globalconvex/zero threshold, actual fullspace step2→3/2/sharp negative-residual endpoint/T4tunedaverageupper5/4/eventualactualaverage<1/10. ALL36unique public/canary names actually checked and axioms audited:19proof+3defs+14proof, standard3-or-none/no sorryAx.19nativeguards notcompilation. Actualfresh focused/publicbody/wholecanary/axes/guards passed, but explicitroot/Tests/fullharness/contributor/site/registry/finalreader/PR stillpending. Source interpretation acceptedCONTRACT separately; reader corrections remain to apply after this verdict. Identify mathematical repairs separately from required readercorrections, never change/quietlyweaken inputs.

Old20261003source receipts historicalonly; currentrestrictedblindpacketdoesnot erase actorpriorhistory; three distinct automatedactorsrequestedAstra/medium/nohuman/external/runtimeattestation. Singlelowerreuse route, native commandgates versus prompt/fileconventions distinct. Actual22scope nodes2954direct references include definitions, notfull/canary graph;18source-localproofvaluepairs+sharedfixedOGDpair audited. Exactstacked OPENdraft16452f628a7...; main6847b...unchanged;legacy11beforepackage→10ONLYOnlineHuberafterallgates;Chapter1migration/Chapter2mandatorytotalnull/incomplete/wholeGoalACTIVEunbudgeted. Othermandatoryalreadycompiledbutunauditedbodies remain; noChapter3competition/merge/deploy/retirement. Write ONLY public-body-review-v1.md and public-body-receipt-v1.json with actor.task=/root/source_reviewer,19targetverdicts/seven slots/actualproducerdecisions/source-implicitthreshold/one-sidedfamily/canaries/required_reader_corrections and mathematical_repairs separately/ALLreviewed_files/reportSHA.''')
paths={row['path'] for row in load(run/'contract-source-inputs-v1.json')['rows']};paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
write('public-body-inputs-v1.json',dict(scope='19retained Huber producer/terminal bodies,3full defs,whole14canaryproofs/36namedaxes',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Actual Huber19bodies/3defs/whole14canaries/36axes/19guards frozen; distinct BODY pending.')
