"""Bind actual public comparison proofs, all canaries and named audits for distinct BODY review."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-GUESSING-MIGRATION-20261006'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
labels=['focused-v2-01','root-v1-01','public-canaries-v1-01','public-axioms-v1-01','public-scoped-graph-v1-01','verify-public-fences-v1-01']
for n in labels:assert load(run/(n+'-exit.json'))['exit_code']==0,n
freeze=load(run/'draft-freeze-v2.json');headers=load('docs/contracts/online-guessing-migration-v1/headers-native-v2.json')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
for p in freeze['module']:
 assert Path(p).read_bytes().endswith((run/('original-'+Path(p).name+'.txt')).read_bytes())
 assert tokens(Path(p).read_text(encoding='utf-8'))==tokens((run/('original-'+Path(p).name+'.txt')).read_text(encoding='utf-8'))
for n,row in headers.items():assert hashlib.sha256(lean_declaration_header(Path(row['file']),n).encode()).hexdigest()==freeze['headers'][n]
for p,h in freeze['canary'].items():assert sha(p)==h
strip_directives=lambda t:re.sub(r'(?m)^#(?:check|print)\b[^\n]*\n','',t)
assert tokens(Path('BanditRLProof/OnlineGuessingComparison.lean').read_text(encoding='utf-8'))==tokens(strip_directives((run/'leaves/gap-unbounded-v1.lean').read_text(encoding='utf-8')))
r=load(run/'source-contract-receipt-v1.json');assert sha(r['report'])==r['report_sha256']
snap={(row['path'],row['raw_sha256']):row['snapshot'] for row in load(run/'historical-raw-supersession-v1.json')['rows']}
prior=[]
for row in r['reviewed_files']:
 p,h=row['path'],row['sha256'];resolved=p if sha(p)==h else snap[(p,h)];assert sha(resolved)==h
 prior.append(dict(path=p,sha256=h,resolved=resolved))
write('prior-contract-binding-v1.json',dict(status='passed',rows=prior,original_receipt_immutable=True,explicit_root_Tests_new_imports_and_comment_supersession=True))
raw=(run/'public-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
names=load(run/'public-named-declarations-v1.json')['axiom_probe'];assert len(matches)==21 and {n for n,a in matches}==set(names)
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
gp=Path('tmp/online-guessing-migration-public-graph-v1.json');g=load(gp)
assert g['extraction']['source']=='compiled-environment' and len(g['nodes'])==13
assert sum(n['kind']=='theorem' and n['has_value'] for n in g['nodes'])==12 and sum(n['kind']=='definition' and n['has_value'] for n in g['nodes'])==1
pairs=[[e['source'],e['target']] for e in g['edges'] if e['kind']=='value' or e['also_in_value']]
for a,b in [('guessing_vs_mean_lower','meanPredict_zero_cumulativeLoss'),('guessing_vs_mean_lower','guessing_squared_horizon_lower'),('guessing_vs_mean_unbounded','guessing_vs_mean_lower'),('example_2_14','equation_2_1')]:
 assert ['BanditRL.OnlineGradientDescent.'+a,'BanditRL.OnlineGradientDescent.'+b] in pairs,(a,b)
(run/'compiled-public-graph-v1.json').write_bytes(gp.read_bytes())
write('public-actual-bindings-v1.json',dict(status='actual-public-body-candidate',public_modules={p:sha(p) for p in set(row['file'] for row in headers.values())},headers=freeze['headers'],old_canaries=freeze['canary'],new_canary={'Tests/OnlineGuessingComparisonCanary.lean':sha('Tests/OnlineGuessingComparisonCanary.lean')},axioms=axioms,named_axiom_count=21,native_guards=12,retained_proofs=9,retained_definitions=1,new_proofs=3,new_definitions=0,canary_proofs=6,canary_definitions=2,actual_scope_nodes=13,actual_scope_edges=len(g['edges']),graph_sha256=sha(gp),project_value_pairs=[p for p in pairs if p[0].startswith('BanditRL.') and p[1].startswith('BanditRL.')],full_graph_export=False,canary_graph_export=False,actual_passed_gates=labels,root_jobs=9089,source_package_accepted=False,chapter_complete=False,goal_complete=False,proof_repairs=[],import_parser_repair='New leading module-doc marker before imports -> ordinary block comment; failed source/log exactbytes retained; all12headers and allproof tokens same',body_review_pending=True,reader_site_full_harness_pending=True))
subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'public-comparison-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','lower','--kind','build','--status','compiled','--run-id',run.name,'--attempt-id','GUESSING-COMPARISON-V1','--lean','BanditRLProof/OnlineGuessingComparison.lean','--statement-hash',freeze['headers']['guessing_vs_mean_unbounded'],'--new-declaration','BanditRL.OnlineGradientDescent.guessing_vs_mean_unbounded','--verifier-evidence',str(run/'public-axioms-v1-01.log'),'--progress-class','terminal','--notes','Actual3new comparison bodies plus9retainedproofs1definition/fresh root9089/canaries21namedaxes12guards. Frozen arbitrary-threshold source comparison terminal closed, distinct BODY/package acceptance still pending; not chapter/book/productivity experiment.'],check=True)
write('public-body-review-packet-v1.md','''Required distinct BODY review, GPT-6 Astra/medium requested. Independently hash ALL public-body-inputs-v1.json rows and resolve144 prior source rows through prior-contract-binding-v1/exact raw snapshots. Source Example2.14 printed15/PDF27/source mean predictor/Theorem1.3 p4/PDF16, current restricted12target reconstruction. ALL12nativev2headers match;9retainedprooftokens/unitInterval unchanged, old2wholecanaries bytefixed. NEW3actual bodies ported from separately successful scratch leaves, exact proof tokens same, no desired regret/stability/divergence oracle. Current actual compiled13node graph/edgecount directtype/value includingdefinitions, notfull/canary graph. Inspect real reuse pairs, not teaching arrows inferred as dependencies.

Retained genuine projection/clamp/ambient gradient/global square regularity/uniform feasible gradient norm2 -> same causal known-horizon OGD/tuned2sqrtT for all feasible initial/comparator; printed O(sqrtT)/derivedconstant2. Genuine clamp geometric zero-label trajectory initial1/positive n/sourceeta/T=(2n)^2 -> Bernoulli firstn>=1/2 -> n/4 lower/sqrtT8. eta identity n0 permits totaldivision algebra only, no tuned zero-horizon guarantee. Source labels are real[0,1], unrestricted helper regimes visible, stronger historical RegularLoss discharged globally rather than assumed as source premise.

NEW produced finite sum: actual meanPredict initial1/2 and then empiricalMean of zero STRICTPREFIX; unfold true definitions/finite conditional sum, cumulative square loss exactly1/4 for every positiveT, not a stipulated sequence/stability bound. Source comparator0 has actual zero optimal squared loss on this stream. For n>0 the source horizon is positive; produced mean loss and ACTUAL old OGD lower prove true gap n/4-1/4. Actual exists_nat_gt(max(4*C+1,(N:real))) yields natural n>N/positive n and strict real threshold, then actual gap lower gives forall C real, N natural, exists n>N gap>C. No positivity premise on C inserted, no future-label optimization, no assumed divergence. The public terminal is unbounded-tail EXISTS, not formal Tendsto/to-all-large-n statement, even if a stronger consequence follows from lower bound. It is an algorithm family known-horizon for each n, NOT one anytime run. Same zero stream but OGDinit1 vs meaninit1/2, NOT equal-initialization/every-stream/every-init/minimax/Chapter4 theorem; three derived supporting refinements not printed source statements. No whole Chapter1 migration accepted from this dependency.

Whole old5canaryproofs2defs fixed: step1 clippingabove/below distinct from T4eta1/4 upper bound4; n4T64eta1/16 genuine firstpoint7/8/lower1. NEW actual same-stream gapcanary n4T64eta1/16 gap>=3/4 uses both actual algorithms/newlower. Complete21unique names12publicproofs+1domain+6canaryproofs+2canarydefs standard3-or-none/no sorryAx;12nativeguards notcompilation. Fresh focusedv2/root9089/publicwhole3canaries/axioms/scopedgraph passed. Initial focusedv1 failed import parsing from newly added leading /-! docblock; exactbeforebytes/log retained, only marker changed to ordinary /-, same allproof/header/canary tokens. Plannedhash v1 raw→nativev2 normalization metadata-only; source helperv1 failed oldOGDacceptedv1 guessedpath, v2actualpath/resumechecks preserved. No mathematical proof repair.

Eight source-contract reader corrections remain pending; identify reader fixes separately from mathematical repairs. Source body acceptance is distinct from full Tests/harness/contributor/history/site/registry/finalreader/PR gate, not yet done. One source Example2.14/twelvepublicproofs9retained3new1retaineddef, not12newprintedtheorems. Sharedgraph/new3proofnodes onlyif registry verified, sameBook/root/toolchain. Stacked OPENdraft163 exact25c77a837c849eb78832673063483db5f663a73a, notmain; Chapter2totalnull/incomplete/wholeGoalACTIVEunbudgeted/legacy13beforepackage/no merge/live/retirement. Three required automated roles requestedmedium, historynoterased/nohuman/external/runtime attestation. Command-enforced gates and role/prompt/file conventions distinct. Global reference-index rewrite notrun outside bounded window, actual read-onlyretrieval/API/compiledgraphs fresh. Write ONLY public-body-review-v1.md/public-body-receipt-v1.json here, actor.task=/root/source_reviewer,12target_verdicts/sevenslots/actualproducers/canaries, mathematical_repairs versus required_reader_corrections, ALL reviewed_files/reportSHA. Do not edit inputs or accept chapter/book/main/live.''')
paths={row['path'] for row in load(run/'contract-source-inputs-v1.json')['rows']}
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
paths.update(['BanditRLProof/OnlineGuessingComparison.lean','Tests/OnlineGuessingComparisonCanary.lean',gp.as_posix()])
for p in paths:assert Path(p).is_file(),p
write('public-body-inputs-v1.json',dict(scope='12actualpublicbodies9retained3new+1domain/whole3canaries6proofs2defs/21axes12guards; source/body/package separate',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Actual public proof bundle/source bindings frozen;3new genuine comparison bodies, BODY review pending.')
