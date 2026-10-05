"""Accept only the exact current source package after distinct final verdict."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-CLOSED-PROPER-MIGRATION-20261006';cache={}
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):
 key=str(p)
 if key not in cache:cache[key]=hashlib.sha256(Path(p).read_bytes()).hexdigest()
 return cache[key]
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
history=load(run/'history-binding-audit-v1.json')
snapshots={(row['path'],row['raw_sha256']):row['resolved_raw_file'] for row in history['rows']}
for row in load(run/'historical-raw-supersession-v1.json')['rows']:
 assert sha(row['snapshot'])==row['raw_sha256'];snapshots[(row['path'],row['raw_sha256'])]=row['snapshot']
rows=[];final=None
for name in ['source-contract-receipt-v1.json','public-body-receipt-v1.json','final-reader-receipt-v1.json']:
 receipt=load(run/name);assert receipt['actor']['task']=='/root/source_reviewer' and receipt['verdict'] in ['accepted','accepted-with-explicit-delta']
 assert not receipt.get('mathematical_repairs',[]) and not receipt.get('required_repairs',[]) and sha(receipt['report'])==receipt['report_sha256']
 reviewed={row['path']:row['sha256'] for row in receipt['reviewed_files']}
 if name=='final-reader-receipt-v1.json':
  final=receipt
  for row in load(run/'final-reader-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256'],row['path']
 for p,h in reviewed.items():
  resolved=p if sha(p)==h else snapshots[(p,h)];assert sha(resolved)==h,p
  rows.append(dict(receipt=name,path=p,sha256=h,resolved=resolved))
integrated=load(run/'integrated-gates-overlay-v1.json')
for label in integrated['actual_passed_gates']:assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineClosedProper.lean');original=(run/'original-OnlineClosedProper.lean.txt').read_bytes()
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert public.read_bytes().endswith(original) and tokens(public.read_text(encoding='utf-8'))==tokens(original.decode('utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
for p,h in dict(freeze['canary'],**freeze['root_Tests']).items():assert sha(p)==h,p
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
boundary=dict(source_package_accepted=True,chapter_complete=False,goal_complete=False)
write('accepted-binding-audit-v1.json',dict(status='passed',raw_review_rows=len(rows),rows=rows,all_final_fixed_inputs_rechecked=True,frozen_headers=freeze['headers'],all_original_proof_definition_tokens_canary_root_Tests_fixed=True,prior_final_history_bindings='history-binding-audit-v1.json',prior_accepted_reports_receipts_unmodified=True))
delta='Source Euclidean/stated Hausdorff sufficient scope specializes stronger arbitrary-topological Lean scope, not assumptions equivalence/T2 necessity. REAL thresholds/both infinity values, bottom-density union/topempty, no no-bottom/properness/convexity/closed-epigraph substitute. SourceProper core has no topology but actual properiff keeps TopologicalSpace. SAMEcanonical0/top indicator/direct cuts/finite witness; emptyambient allclosed/noneproper, fullindicatorproper iffambientnonempty. Three independent retained proofs/no mutual theorem value edges; teaching order distinct from term graph.'
write('accepted-decision-v1.json',dict(status='accepted-with-explicit-delta',scope='Orabona v10 four numbered anchors plus REQUIRED unnumbered closedness/LSC equivalence, retained closed/proper source integration',source_anchor='Definitions2.16/2.18, Examples2.17/2.19 and unnumbered equivalence; printed16/PDF28',source_numbered_anchors=4,source_unnumbered_required_results=1,frozen_headers=freeze['headers'],explicit_delta=delta,retained_public_proofs=3,retained_public_definitions=2,new_public_proofs=0,new_definitions=0,public_canary_proofs=6,public_canary_definitions=0,named_axiom_audits=11,native_guards=3,new_registry_nodes=0,old_registry_IDs_URLs_preserved=10809,root_jobs=9089,Tests_jobs=9232,full_tests=466,existing_skips=7,root_Tests_execution_overlapped=False,build_boundary=integrated['execution_boundary'],site_source_commit=load(run/'registry-v1.json')['source_commit'],stacked_base='f989706461cb466bc290261f4845f113621e807d',stacked_base_PR=165,final_review_receipt='final-reader-receipt-v1.json',final_review_report_sha256=final['report_sha256'],compiled_scope_graph='compiled-retained-graph-v1.json',compiled_scope_nodes=5,compiled_scope_edges=213,full_graph_export=False,canary_graph_export=False,mathematical_repairs=[],nonmathematical_repairs=integrated['failure_repairs'],reader_corrections='Seven CONTRACT/BODY corrections applied and distinctly rechecked.',main_relative_gate=integrated['main_relative_gate'],full_whitespace_gate=integrated['full_whitespace_gate'],scoped_whitespace_gate=integrated['scoped_whitespace_gate'],chapter_mandatory_total=None,PR_delivery_pending=True,merged=False,live=False,**boundary))
write('accepted-obligations-v1.json',dict(required=[dict(name=n,statement_hash=h,state='accepted-source-foundational-equivalence') for n,h in freeze['headers'].items()],source_numbered_anchors=4,source_definitions=2,source_numbered_indicator_examples=2,source_unnumbered_required_results=1,new_proofs=0,new_definitions=0,remaining_chapter_legacy_migrations=9,legacy_migrations_before=10,exact_accepted_legacy_delta='ONLYOnlineClosedProper;3retainedproofs2definitions are not3new printed results or proof-count gain.',chapter_total=None,future_chapters='3-16 unenumerated mandatory',main_missing_changed_production_contract_paths=9,**boundary))
named=load(run/'public-named-declarations-v1.json');names=named['public_proofs']+named['public_definitions']
write('source-inventory-acceptance-overlay-v1.json',dict(base_inventory='docs/contracts/online-book-v1/source-inventory.json',base_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'),additive_only=True,source_anchor='Definitions2.16/2.18, Examples2.17/2.19 and unnumbered equivalence p16/PDF28',source_numbered_anchors=4,source_unnumbered_required_results=1,accepted_public_names=names,retained_proofs=3,retained_definitions=2,new_proofs=0,delta=delta,**boundary))
manifest='research-wiki/contribution-contracts/online-closed-proper-migration-20261006.json'
write('contribution-acceptance-overlay-v1.json',dict(manifest=manifest,manifest_sha256=sha(manifest),source_contract='source-contract-receipt-v1.json',body='public-body-receipt-v1.json',reader='final-reader-receipt-v1.json',integrated='integrated-gates-overlay-v1.json',accepted_decision='accepted-decision-v1.json',semantic_status='accepted-with-explicit-delta',earlier_candidate_pending_fields_superseded_additively=True,**boundary))
digest='Only four numbered anchors/two definitions/two indicator examples plus required unnumbered equivalence accepted;3retainedproofs2complete definitions/0newmathcode,nodes. '+delta+' Whole6canaryproofs/11named standard3-or-none axes/no sorryAx/3guards,5nodes213direct references notfull/canaryexport. Sequentialroot9089Tests9232/full466tests7skips/exactstackedcontribution/scopedCRLFawarewhitespace/history/cleanlocalsite5canonicalnodes10809oldIDsURLs0new/actualfirstviewportpassed; sevenreaderfixes distinctly reviewed, failures preserved/no math/test weakening. Legacy10->9ONLYOnlineClosedProper;Chapter1migration/Chapter2mandatorytotalnull/incomplete/wholeGoalACTIVE/mainliveunchanged/PRpending/worktreeretained.'
write('memory-digest-accepted-v1.md',digest)
write('retrieval-index-accepted-v1.md','Accepted3actualheaders/2complete definitions/current11@types/sourceblind/CONTRACT/BODY/FINALreceipts/rawbindings/additiveoverlays. Actual pinned topology open/closed preimage/EReal real-density APIs, sharedcanonicalindicator/directcuts/finitewitness. Whole6canaries/11namedaxes/3guards/rootTestsfull/site5nodes10809IDsURLs/compiled5nodes213directreferences,no mutual3proofedges. RemainingChapter2maintext/necessaryappendix/legacymigrationsrequired/somecompiledbutunaudited;Chapter1migration/wholeGoalACTIVE,noChapter3competitiveproofwriting.')
write('program-milestone-v1.json',dict(total_Goal='Chapters1-16 ACTIVE unbudgeted',bounded_milestone='Four numbered closed/proper anchors plus required unnumbered equivalence source integration accepted',legacy_remaining_before=10,legacy_remaining_after=9,exact_legacy_modules=['OnlineClosedProper'],new_proofs=0,new_definitions=0,new_registry_nodes=0,source_numbered_anchors=4,source_unnumbered_required_results=1,chapter2_mandatory_total=None,Chapter1_complete=False,chapter2_complete=False,chapters3_16='unenumerated mandatory',main_updated=False,live_updated=False,**boundary))
gate('accepted-reviewer-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','reviewer','--kind','review','--status','accepted','--run-id',run.name,'--attempt-id','CLOSED-PROPER-RETAINED-BODIES-V1','--statement-hash',freeze['headers']['sourceClosed_iff_lowerSemicontinuous'],'--reused-declaration','BanditRL.OnlineConvex.sourceClosed_iff_lowerSemicontinuous','--verifier-evidence',str(run/'final-reader-receipt-v1.json'),'--harness','hierarchical','--progress-class','retrieval-reuse','--reviewer-validated','--notes','Same actualcompiled3proof2definition bundle accepted after distinct source/reader/integrated gates. Four numbered anchors+required unnumbered result/0newproofgain, actualsourceintegration notChapter2/book/productivity experiment.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('accepted-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('accepted-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','accepted','--payload-json',json.dumps(dict(run_id=run.name,accepted_decision=str(run/'accepted-decision-v1.json'),retained_proofs=3,retained_definitions=2,new_proofs=0,merged=False,live=False,**boundary)))
gate('accepted-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only closed/proper sourcepackage accepted,Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'sourceClosed_iff_lowerSemicontinuous'),'--declaration','BanditRL.OnlineConvex.sourceClosed_iff_lowerSemicontinuous','--file',public.as_posix(),'--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:BanditRL.OnlineConvex.SourceClosed:compiled','--dependency','lean:BanditRL.OnlineConvex.SourceProper:compiled','--dependency','lean:BanditRL.OnlineConvex.extendedIndicator:compiled','--dependency','review:source-reader:accepted','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--output',str(run/'accepted-frontier-v1.json'),'--shadow-status','pending')
gate('accepted-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-accepted-v1.md'),'--frontier',str(run/'accepted-frontier-v1.json'))
write('native-acceptance-overlay-v1.json',dict(status='passed',accepted_decision='accepted-decision-v1.json',accepted_decision_sha256=sha(run/'accepted-decision-v1.json'),actual_attempt='CLOSED-PROPER-RETAINED-BODIES-V1',frontier='accepted-frontier-v1.json',shadow='accepted-frontier-shadow-v1',**boundary))
print('Only closed/proper sourcepackage accepted; whole GoalACTIVE, stackedPRpending.')
