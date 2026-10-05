"""Record actual comparison candidate after sequential combined Lean gates."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-GUESSING-MIGRATION-20261006'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
freeze=load(run/'draft-freeze-v2.json');headers=load('docs/contracts/online-guessing-migration-v1/headers-native-v2.json')
assert load(run/'body-binding-audit-v1.json')['status']=='passed'
for n,row in headers.items():assert hashlib.sha256(lean_declaration_header(Path(row['file']),n).encode()).hexdigest()==freeze['headers'][n]
for p,h in freeze['canary'].items():assert sha(p)==h
actual=load(run/'public-actual-bindings-v1.json')
for p,h in actual['public_modules'].items():assert sha(p)==h
for p,h in actual['new_canary'].items():assert sha(p)==h
jobs={}
for n in ['root','Tests']:
 assert load(run/(n+'-v1-01-exit.json'))['exit_code']==0
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(n+'-v1-01.log')).read_text(encoding='utf-8'));assert m
 jobs[n]=int(m.group(1))
assert jobs==dict(root=9089,Tests=9232)
assert load(run/'Tests-v1-01-exit.json')['started_at']>=load(run/'root-v1-01-exit.json')['ended_at']
write('proof-obligations-candidate-v1.json',dict(stage='candidate',required=[dict(name=n,statement_hash=h,state='actual-public-body-and-combined-Lean-passed-package-gates-pending') for n,h in freeze['headers'].items()],fixed_new_terminal='guessing_vs_mean_unbounded',retained_proofs=9,new_proofs=3,retained_definitions=1,new_definitions=0,source_package_accepted=False,chapter_total=None,goal_complete=False))
write('candidate-decision-v1.json',dict(status='candidate',retained_proofs=9,new_proofs=3,retained_definitions=1,new_definitions=0,public_canary_proofs=6,public_canary_definitions=2,named_axiom_count=21,native_guards=12,compiled_scoped_nodes=13,compiled_scoped_edges=2113,compiled_graph_sha256=actual['graph_sha256'],root_jobs=9089,Tests_jobs=9232,root_Tests_sequential=True,Lean_files_unchanged_after_gates=True,build_boundary='Fresh successful gate invocations with cached jobs; not clean rebuilding every job.',source_contract_body_accepted=True,corrected_final_reader_pending=True,full_harness_site_registry_PR_pending=True,legacy_before=13,legacy_after_acceptance_only=11,chapter2_total=None,chapter_complete=False,goal_complete=False,merged=False,live=False))
digest='One source Example2.14 plus derived direct comparison.9retainedproofs1domain/3newcomparisonproofs0newdefs. Actual real[0,1] loss/projection/gradient/produced globalregularity/samecausal positive known-horizon OGD, derivedconstant2sqrtT vs printedO(sqrtT). Positive squarehorizons/allzero/OGDinit1/comparator0 true trajectory/lower n/4; meanPredict actualinit1/2/strictprefixmean0/exactloss1/4, actualgap n/4-1/4 and actualArchimedeanwitness forallC real,Nnatural existsn>N gap>C. Different validfixedinit/samestream/known-horizonfamily/tail-existence, not uniform/equal-init/anytime/Tendsto/minimax/Chapter4. Three new frozen scratch/public bodies closed, distinct contract/BODY accepted; wholecanaries6proofs2defs/21namedstandard3-or-noneaxes/12guards. All12headers unchanged nativev2; initial plannedraw→native whitespacefingerprint correction retained. Initialpublicimportdocmarkerparser failure/rawbytes retained, ordinaryblockmarker only/proof tokens unchanged, focusedv2pass. Sourceinputhelper oldOGDguessedacceptedv1path fail retained/actualv2lookup/resumechecked. Corrected8readerfixes selectedsubtree and actualproof_bridge adapter pendingfinalreview. Sequentialroot9089Tests9232passed, scopedcompiled13nodes2113directedges/notfullcanary. Fullharness/contributor/history/site/registry/finalreader/PRpending. Legacy13beforeonlyfuture2modules13→11/not12newproofgain. Chapter1migration/Chapter2null/wholeGoalACTIVE, no merge/live/globalSGBchange.'
write('memory-digest-candidate-v1.md',digest)
write('retrieval-index-candidate-v1.md','Exact12nativev2headers/source/DAG in online-guessing-migration-v1; new actual OnlineGuessingComparison proof bodies/current named audit/logs/canary/compiled13nodes2113directreferences. Actual meanPredict/empiricalMean/strict-prefix/equation2.1/trueclamptrajectory/Bernoulli/finiteconditional sum/exists_nat_gt reused; no prooforacle. Global reference-index notrun outside bounded scope, read-only retrieval/current types/environment used. Current/prior raw snapshots/required distinct automated receipts, source versus3derivedcompares visible. Pendingcandidate package, chapter/book incomplete.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=freeze['headers'],retained_proofs=9,new_proofs=3,new_definitions=0,root_jobs=9089,Tests_jobs=9232,source_package_accepted=False,chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only source Example2.14/actual comparison candidate, Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',headers['guessing_vs_mean_unbounded']['statement'],'--declaration','BanditRL.OnlineGradientDescent.guessing_vs_mean_unbounded','--file','BanditRLProof/OnlineGuessingComparison.lean','--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineGradientDescent.guessing_vs_mean_lower:compiled','--dependency','lean:BanditRL.OnlineGradientDescent.meanPredict_zero_cumulativeLoss:compiled','--dependency','lean:BanditRL.OnlineGradientDescent.guessing_squared_horizon_lower:compiled','--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Actual fixed comparison terminal/candidate sequentialcombined gates recorded, task-onlyfrontier; package pending.')
