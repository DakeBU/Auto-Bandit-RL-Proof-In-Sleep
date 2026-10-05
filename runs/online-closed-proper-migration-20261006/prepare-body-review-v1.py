"""Freeze actual retained Huber elaboration and request a separate body review."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-CLOSED-PROPER-MIGRATION-20261006'
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
freeze=load(run/'draft-freeze-v1.json');module=Path('BanditRLProof/OnlineClosedProper.lean')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(module.read_text(encoding='utf-8'))==tokens((run/'original-OnlineClosedProper.lean.txt').read_text(encoding='utf-8'))
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
names=load(run/'public-named-declarations-v1.json')['axiom_probe'];assert len(matches)==len(names)==11 and {n for n,a in matches}==set(names)
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
write('public-actual-bindings-v1.json',dict(status='freshly-elaborated-retained-body-candidate',public_module={module.as_posix():sha(module)},canary=freeze['canary'],root_Tests=freeze['root_Tests'],headers=freeze['headers'],axioms=axioms,named_axiom_count=11,native_guards=3,actual_passed_gates=labels,retained_proofs=3,retained_definitions=2,new_proofs=0,new_registry_nodes=0,canary_proofs=6,canary_definitions=0,body_review='pending',root_Tests_harness='pending',reader_site_PR='pending',source_terminal_accepted=False,chapter_complete=False,goal_complete=False))
gate('retained-body-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','lower','--kind','build','--status','compiled','--run-id',run.name,'--attempt-id','CLOSED-PROPER-RETAINED-BODIES-V1','--lean',module.as_posix(),'--statement-hash',freeze['headers']['sourceClosed_iff_lowerSemicontinuous'],'--reused-declaration','BanditRL.OnlineClosedProper.huber_average_eventually','--verifier-evidence',str(run/'public-body-v1-01.log'),'--progress-class','retrieval-reuse','--notes','Actual3closed/proper bodies2full definitions/whole6canaries/11namedaxes/3guards passed;0newmathcode/nodes. DistinctBODY and package gates pending, Chapter2/Book incomplete.')
write('public-body-review-packet-v1.md','Distinct BODY review, requested GPT-6 Astra/medium. Independently hash ALL public-body-inputs-v1.json rows and resolve immutable prior-contract-binding-v1.json rows. Re-read exact source printed16/PDF28, three complete actual proof bodies and frozen headers, both complete definitions/actual class contexts, same canonical extendedIndicator, current blind reconstruction, compiled5nodes213direct type/value edges and whole unchanged6canaries. Four numbered anchors plus REQUIRED unnumbered equivalence,3retained proofs2defs/zero new mathcode/nodes. CONTRACT acceptance is separate. Inspect actual finite-cut complements/bottom-realcut-union via EReal.exists_between_coe_real/topempty/reverseclosedpreimages, no missing infinity cuts/no-bottom/properness/convex/T2 assumption. Source Hausdorff sufficient generality vs actual arbitrary topological stronger generality explicit, not sourceequivalence/closedepigraph claim. Exact indicator cuts V if0<=r elseempty and r0 necessity, without calling first theorem; actual graph no theorem-to-theorem edges. Proper finite witness forces membership/member produces0+nowherebottom. Core SourceProper no topology binder, actual properiff DOES retain TopologicalSpace; no Nonempty E/closed/convex/Vnonempty premise for iff, emptyambient admitted. Both infinite values, no toReal shortcut/oracles/wrappers. Whole6proof canary bottom closed/LSC/improper, genuinely nonconstant real[0,1] indicator closed/proper, empty improper. COMPLETE11namedaxes3proof+2defs+6canaryproof, standard3-or-none/no sorryAx,3nativeguards separate from compilation. Fresh focus/publicbody/canary/axes/guards only; rootTests/fullharness/reader/site/PR pending. All actualmath/definitions/canary/rootTests fixed. Single lower review order not fake causal DAG. Same10809IDsURLs expected/0new; exact OPENdraftPR165f989706...stackedbase notmain6847...; old20261003 receipts historical. Three distinct automated roles/requestedAstra medium/restrictedpacket honesty/nohumanexternalruntimeattestation; CLIforced vs prompt/filegates distinct. Legacy10->9ONLYOnlineClosedProper after gates/PR, Chapter1migration/Chapter2null/incomplete/wholeGoalACTIVE. Write ONLY public-body-review-v1.md and public-body-receipt-v1.json actor.task=/root/source_reviewer,3targetverdicts seven slots/bothcomplete definitions/producer and topologybinder decisions/ALLreviewed_files/reportSHA, mathematical_repairs separately required_reader_corrections. Do not modify inputs/accept chapterbook.')
paths={row['path'] for row in load(run/'contract-source-inputs-v1.json')['rows']};paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
write('public-body-inputs-v1.json',dict(scope='3retained closed/proper bodies2complete definitions/whole6canaryproofs/11namedaxes',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Actual closed/proper3bodies/2defs/whole6canaries/11axes/3guards frozen; distinct BODY pending.')
