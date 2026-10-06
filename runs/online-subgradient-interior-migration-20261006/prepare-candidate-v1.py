"""Record compiled exact relative terminal after distinct BODY and sequential combined Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-INTERIOR-MIGRATION-20261006';load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'));sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
assert load(run/'body-binding-audit-v1.json')['status']=='passed';assert load(run/'reader-integration-v1.json')['public_module_unchanged_since_current_build']
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineSubgradientInterior.lean');assert sha(public)==load(run/'public-actual-bindings-v1.json')['module_sha256']
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
assert load(run/'Tests-v1-01-exit.json')['started_at']>=load(run/'root-v1-01-exit.json')['ended_at']
ob=load(run/'proof-obligations-proving-v1.json');ob['stage']='candidate'
for row in ob['required']:row['state']='exact terminal compiled, distinct BODY accepted, package gates pending'
ob.update(actual_new_proofs_compiled=2,retained_proofs=1,fresh_combined_jobs=jobs,public_canary_proofs=4,named_kernelchecks=8,native_guards=3)
write('proof-obligations-candidate-v1.json',ob)
digest='Persistent Chapters1–16 Goal ACTIVE/unbudgeted, only mandatory ambient+relativeinterior existence package candidate. Exact3terminalheaders/zero numberedanchors/two sourcebranches;1retainedambientproducer+2NEW mathematical proofs (relative affineCONTACT at prescribedx then global Riesz vector), no newdefs. IntrinsicInterior of originaldomain affineSpan, no closure/fullD replacement. Actualrestriction/contact/linearextend/finiteDcontinuous/intercept/contactoriginalx/globalqueriesincludingtop/Rieszcomplete_of_proper; sourceproperness retained/helperfinitewitness derivable. No support/minorant/contact/diff oracle. Four old/newgenuinecanaryproofs (interval,nonclosednonconstantraycontact,singletonrelativevector,emptyambientinterior),8namedstandard-or-none kernelchecks/3nativeguards. Actual8selectednodes1193directrefs/7requiredvaluepairs/no directdonorvalueedge/old2nodesexact/notfullregistrygraph. DistinctCONTRACT/BODY accepted and nine readerrequirements applied. FreshsequentialrootTests passed/currentLeancodeunchanged; fullharness/contributor/site/registry/final/PRpending, cachedjobsnotallclean. Expectedall10809oldIDsURLs+2newcanonicalmathproofnodes aftergates. Legacy8->7ONLYInteriorafteracceptancePR, newproofgrowthseparate. Chapter1migration/Chapter2mandatorytotalnull/incomplete/T2.22T2.23mandatorylater/future3–16unenumerated/wholeGoalACTIVE/noChapter3competition/no merge/deploy/live/retirement. Actual nativecommandgates vsfilepromptconventions separate; three automatedactors requestedAstra medium/nohumanexternalruntimeattestation. Readonly/preparationerrors preserved, no math/Leanrepair/terminalchange. Scopedretrieval fresh/globalindexrewrite notrun.'
write('memory-digest-candidate-v1.md',digest);write('retrieval-index-candidate-v1.md','Actual frozenheaders/currentpublictypes/intrinsicInterior_subset/singleton/mem_intrinsicInterior/convex-domain ri API/affinevaddorigin/homeomorphpreimageinterior/canonicalambientCONTACT/LinearMap.exists_extend/finiteDtoContinuousLinearMap/Riesz complete_of_proper. Actual8selectednodes1193references and genuinecanaryvaluecalls; sourceCONTRACT/BODY immutable/currentreaderqualifications. New2proofgrowth distinctfrom1legacy migration; packagepending/noChapter2completion/globalreferenceindexrewrite notrun.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()];write('candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=1,new_proofs=2,frozen_headers=freeze['headers'],fresh_jobs=jobs,actualselectedgraphnodes=8,actualselectedgraphedges=1193,remaining_gates=['fullharness','contributor','site/registry/finalreview','raw/PR'],source_package_accepted=False,chapter_complete=False,goal_complete=False)))
gate('frontier-refresh-help-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--help')
gate('frontier-shadow-help-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--help')
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only ambient-relative existence package candidate, Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'subgradient_exists_of_relative_domain_interior'),'--declaration','BanditRL.OnlineConvex.subgradient_exists_of_relative_domain_interior','--file',str(public),'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineConvex.affine_support_of_relative_domain_interior:compiled','--dependency','lean:BanditRL.OnlineConvex.affine_support_of_domain_interior:compiled','--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Actual sequential combined Lean gates bound; source candidate and task-only shadow recorded, wholeGoal ACTIVE.')
