"""Freeze actual retained closed/proper elaboration and request a separate body review."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-BASIC-MIGRATION-20261006'
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
freeze=load(run/'draft-freeze-v1.json');module=Path('BanditRLProof/OnlineSubgradientBasic.lean')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(module.read_text(encoding='utf-8'))==tokens((run/'original-OnlineSubgradientBasic.lean.txt').read_text(encoding='utf-8'))
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
names=load(run/'public-named-declarations-v1.json')['axiom_probe'];assert len(matches)==len(names)==6 and {n for n,a in matches}==set(names)
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
write('public-actual-bindings-v1.json',dict(status='freshly-elaborated-retained-body-candidate',public_module={module.as_posix():sha(module)},canary=freeze['canary'],root_Tests=freeze['root_Tests'],headers=freeze['headers'],axioms=axioms,named_axiom_count=6,native_guards=2,actual_passed_gates=labels,retained_proofs=2,retained_definitions=1,new_proofs=0,new_registry_nodes=0,canary_proofs=3,canary_definitions=0,body_review='pending',root_Tests_harness='pending',reader_site_PR='pending',source_terminal_accepted=False,chapter_complete=False,goal_complete=False))
gate('retained-body-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','lower','--kind','build','--status','compiled','--run-id',run.name,'--attempt-id','SUBGRADIENT-BASIC-RETAINED-BODIES-V1','--lean',module.as_posix(),'--statement-hash',freeze['headers']['theorem_2_21'],'--reused-declaration','BanditRL.OnlineConvex.theorem_2_21','--verifier-evidence',str(run/'public-body-v1-01.log'),'--progress-class','retrieval-reuse','--notes','Actual2subgradient bodies1complete definition/whole3canaries/6namedaxes/2guards passed;0newmathcode/nodes. DistinctBODY/package gates pending Chapter2/Book incomplete.')
write('public-body-review-packet-v1.md','Distinct BODY review requested GPT-6 Astra/medium. Independently hash ALL public-body-inputs-v1.json rows, resolve immutable prior-contract-binding-v1.json. Read exact source printed16-17/PDF28-29, actual complete2proof bodies/one full SourceSubdifferential definition/two frozenheaders/actual classes/currentblind/current3nodes320direct type-valuegraph/wholeunchanged3canaries. Definition2.20 explicitly proper f; generic predicate ALL EReal wider specialization, bottom/top supports all g; domain includesbottom generically but SourceProper excludes it. Original00context inaccurate sourceprose explicitly corrected before stabilization byv2 and audit, never silently overwritten. point_finite uses actual finite global witness and support, drops source convexity (stronger theorem), no closedness/diff/oracle; universal x,g exactly supplies domain subset/outside emptiness, review this conversion. T2.21 globallyREAL f, ConvexV, for every x inV exists global support forall ambienty; supports are legitimate source hypothesis, no desiredfunctionConvexOn input/producedexistence claim. Actual support at convexcombination plus nonnegative weights incl0/1 and inner cancellation produces ConvexOn. No merelyfiniteonV EReal/generalconvexexistence claim. Normed/inner classes supplyzero/nonemptyE; Vempty allowed, no CompleteSpace/FiniteDimensional. Two independent leaves shareS/no mutual theorem valueedges; 2printedanchors plus1required unnumbered observation, not2newprintedtheorems. All6namedaxes2proof+1complete def+3canary, standard3-or-none/no sorryAx;2nativeguards separate fromcompile. Whole3genuine canaries allreal quadraticglobal2x support, theorem convexsquareuniv, proper interval indicator outside2 no support forallg. Freshfocus/body/canary/axes/guards only, combinedrootTests/fullharness/reader/site/PR pending. Mathematicaltokens/headers/full definition/wholecanary/rootTests unchanged. Source interior existence+relativeinterior footnote/T2.22/T2.23 REQUIRED separate. Singlelower route/three distinct automated actors requestedAstra medium, no independenthumanexternal review/runtime attestation.0new mathcode/nodes/same10809IDsURLs. ExactOPENdraftPR166283e359...base, main6847...unmerged; legacy9->8ONLYOnlineSubgradientBasic aftergatesPR, Chapter1migration/Chapter2null/incomplete/wholeGoalACTIVE. Write ONLY public-body-review-v1.md/public-body-receipt-v1.json actor.task=/root/source_reviewer,2targetverdicts7slots/full definition/deltas/domainconversion,ALLreviewed_files/reportSHA, mathematical_repairs vs required_reader_corrections separate. Inputs immutable, do not acceptChapterGoal.')
paths={row['path'] for row in load(run/'contract-source-inputs-v1.json')['rows']};paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
write('public-body-inputs-v1.json',dict(scope='2retained subgradient bodies1complete definition/whole3canaryproofs/6namedaxes',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Actual subgradient2bodies/1definition/whole3canaries/6axes/2guards frozen; distinctBODY pending.')
