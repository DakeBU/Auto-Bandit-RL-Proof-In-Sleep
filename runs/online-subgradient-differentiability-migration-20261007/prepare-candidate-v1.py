"""Bind actual post-comment sequential combined gates before package candidate state."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-DIFFERENTIABILITY-MIGRATION-20261007'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'));sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
 p=run/n;assert not p.exists(),p
 p.write_bytes((x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
assert load(run/'body-binding-audit-v1.json')['status']=='passed'
assert load(run/'integrated-public-guard-audit-v2.json')['status']=='passed'
public=Path('BanditRLProof/OnlineSubgradientDifferentiability.lean');freeze=load(run/'draft-freeze-v1.json')
assert sha(public)==load(run/'public-comment-qualification-v1.json')['qualified_sha256']
assert (run/'original-OnlineSubgradientDifferentiability.lean.txt').read_bytes() in public.read_bytes()
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
jobs={}
for label in ['root-v2-01','Tests-v2-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
assert load(run/'Tests-v2-01-exit.json')['started_at']>=load(run/'root-v2-01-exit.json')['ended_at']
ob=load(run/'proof-obligations-proving-v1.json');ob['stage']='candidate'
for row in ob['required']:row['state']='exact retained terminal compiled, distinct BODY accepted, package gates pending'
ob.update(retained_proofs=11,new_production_proofs=0,complete_definition_fixed=True,fresh_combined_jobs=jobs,public_canary_proofs=9,named_kernelchecks=20,native_guards=11,actual_selected_graph_nodes=21,actual_selected_graph_directrefs=3026)
write('proof-obligations-candidate-v1.json',ob)
digest='Persistent Orabona Chapters1-16 Goal ACTIVE/unbudgeted; only T2.22 package candidate. One numberedsourceanchor/11retainedproofs1complete realgermdefinition/zero newproduction mathematics or registry nodes. Main iff onlyconvexEReal/pointfinite, no suppliedproper/interior/closed/Lipschitz; true ambientfinitegerm notsmoothcast/relative derivative; everyrealrepresentative exactgradient. Reverseactualnormalperturbation/interior/noBottom/localbounds/nontrivialfilterlimits/compactness/selectedsupportconvergence/twoinequalities/littleO; forwardactualfinite-neighborhoodcontact/global2.7/localmin/Rieszinjectivity. FiniteDproofs/complete derived/zeroDallowed; definition itselfnoFD; allambientqueries/topoutside; proofselection notalgorithm. Sixoldgenuinecanaries+threeNEWTESTdiagnostics singletontoReal smooth/genuinegermfalse/everyg supports; REALsingletonemptyinterior notzeroDclaim. Actual20namedstandard-or-none kernelchecks/11nativeguards,21selectednodes3026directrefs/20valuepairs/old12node1880readinessexact, notfullgraph. Distinct CONTRACT/BODY accepted/nine readerfixes applied/currentpost-comment sequentialrootTests passed, cachedjobsnotallclean. Onlyleadingignoredcomment/originalmathbytecontiguous, no sourceheader/definition changes; firstTESTAPI failure preserved/fixedv2, schemaenumpre-gate metadata correction/sourcehelper/rendering/patherrors preserved. Fullharness/exactcontributor/history/site/registryFINAL/PRpending; same10811oldIDsURLs0newexpected. Legacy7->6ONLYcurrentmodule AFTERacceptedPR; Chapter1migration/nineothermaincontracts/Chapter2totalnullincomplete/T2.23andlaterrequired/Chapters3-16unenumerated/wholeGoalactive. No competingChapter3/merge/deploy/mainlive/globalSGBchange/retirement. Requested three distinctautomatedactorsAstra medium/honestrestrictedhistory/nohumanexternal/runtimeattestation; nativecommandgates vsfilepromptconventions distinct.'
write('memory-digest-candidate-v1.md',digest)
write('retrieval-index-candidate-v1.md','Current exact elevenheaders/fullSourceDifferentiableAt/@types/pinned APIs/actualproducer bodies: supporting_functional_at_closure/affine_support_of_finite_neighborhood/theorem2.7/locallyLipschitzOn_interior/compactball unique mapcluster/NeBot filter/littleO/Riesz/realgerm eventualequality. Native retrieval-record-v1/currentlocaldecl memory lookup;21selectedcompilednodes3026refs/currentrealboundarydiagnostics. SourceCONTRACT/BODY immutable; historicalbindings/rawsnapshots retained; global referenceindex rewrite notrun. OneT2.22terminal source package candidate, zero newproductionmathnodes; laterT2.23mandatory.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=11,new_production_proofs=0,frozen_headers=freeze['headers'],fresh_jobs=jobs,actualselectedgraphnodes=21,actualselectedgraphedges=3026,remaining_gates=['fullharness','contributor/history','site/registry/finalreview','raw/PR'],source_package_accepted=False,chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only T2.22 iff/gradient candidate; Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'theorem_2_22'),'--declaration','BanditRL.OnlineConvex.theorem_2_22','--file',public.as_posix(),'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineConvex.theorem_2_22_gradient:compiled','--dependency','lean:BanditRL.OnlineConvex.singleton_subdifferential_hasGradientAt:compiled','--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Actual post-comment sequential combined gates bound; package candidate/task-onlyshadow, wholeGoal remainsACTIVE.')
