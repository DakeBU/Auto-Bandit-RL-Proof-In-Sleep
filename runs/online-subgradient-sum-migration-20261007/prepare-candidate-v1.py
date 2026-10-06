"""Bind actual post-comment sequential project gates and a task-only candidate frontier."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-SUM-MIGRATION-20261007'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p
 p.write_bytes((x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
assert load(run/'body-binding-audit-v1.json')['status']=='passed'
assert load(run/'integrated-public-guard-audit-v1.json')['status']=='passed'
public=Path('BanditRLProof/OnlineSubgradientSum.lean');freeze=load(run/'draft-freeze-v1.json')
assert sha(public)==load(run/'public-comment-qualification-v1.json')['qualified_sha256']
assert public.read_bytes().endswith((run/'original-OnlineSubgradientSum.lean.txt').read_bytes())
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
assert load(run/'Tests-v1-01-exit.json')['started_at']>=load(run/'root-v1-01-exit.json')['ended_at']
ob=load(run/'proof-obligations-proving-v1.json');ob['stage']='candidate'
for row in ob['required']:row['state']='fixed retained terminal compiled; distinct BODY accepted; package gates pending'
ob.update(fresh_combined_jobs=jobs,complete_definition_fixed=True,canary_proofs=20,canary_definitions=3,named_kernelchecks=29,native_guards=9,selected_graph_nodes=33,selected_graph_directrefs=2844,new_production_proofs=0)
write('proof-obligations-candidate-v1.json',ob)
digest='Persistent Chapters1-16 Goal ACTIVE/unbudgeted. ONE T2.23 anchor/TWObranches;9retainedproduction proofs1complete simultaneous vector definition/0newmath or TESTs. Inclusion arbitrary proper Fintype, no convex/commonfinite/queryfinite; empty-index library extension only. Generic S extends printed proper-function definition: disjoint proper domains give identicallytop aggregate/Sallvectors/Mempty, not aggregateproper. NoBottom legitimizes ordinary addition versus top-dominant upperAdd. Equality positiveFin(n+1), ALL proper/convex/CLOSED, independentz lastDOMAIN+allOTHER AMBIENTinteriors; lastboundary/singleton conditionvacuity kept. Actual separation image/supportcontact/nonzero L/c<=0+interior forces c<0/Riesz actual p,g-p; prefixinterior/properness and aggregate support derive query/componentfinite; recursive equality/Fin.snoc builds actualG. Sixvector proofs actualfiniteDrealinner/derivedcomplete/zeroD;3scalar noE/fullMnoFD. Whole20oldcanaries3defs fixed; nonzero threecomponent/lastboundary/outsideempty/REALsingleton7/inclusionconstraint2/emptyindex0, concave absence not namednonconvexity/inclusion invocation.29kernel standard-or-none/9nativeguards/33selectednodes2844refs22pairs/readiness10nodes1146refs exact, notfullgraph. Distinct CONTRACT/BODY accepted11readerfixes; originalfourroute/allten canonical links/10811oldIDsURLs0newexpected. Postcomment rootTests sequential PASS/cachedjobs. Fullharness/contributor/history/siteFINAL/PR separately pending; old failures/unusedversions/read diagnostics retained. Only ordinaryleadingcomment/rawmathsuffix+selected3JSON/manifest changed; shareddeps/pins/rootTests/oldcanary fixed. Native gates versus file/prompt conventions separate/three distinctautomated actors requested Astra medium/nohumanexternalruntime attestation. GlobalSGBunchanged/taskshadowonly. Legacy6->5ONLYSum AFTERactual PR. NineOTHERChapter1contractgaps/remainingChapter1/2/appendix mandatory; Chapter2 totalnull/incomplete/3-16unenumerated/wholeGoalACTIVE. NextExample2.24required, no Chapter3 competingwrites/merge/deploy/mainlive/retirement.'
write('memory-digest-candidate-v1.md',digest)
write('retrieval-index-candidate-v1.md','Actual9headers/fullM/@types/pinned19APIs, supporting_functional_at_closure/epigraph product image/interior localmax/Riesz/EReal noBottom/Fin.snoc. Native retrieval-record/current scoped CLI searches, 33compiled selectednodes2844refs/22producer-canary pairs/10node1146readiness; not full graph or compatible Optlib rebuild. Current CONTRACT/BODY raw receipts immutable; exact history snapshots retained. Global reference-index rewrite not run. T2.23 only, adjacent2.24+mandatory.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=9,new_production_proofs=0,frozen_headers=freeze['headers'],fresh_jobs=jobs,remaining_gates=['fullharness','contributor/history','site/registry/FINAL','raw/PR'],source_package_accepted=False,chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; T2.23 bothbranches candidate only; chapter/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'theorem_2_23_equality'),'--declaration','BanditRL.OnlineConvex.theorem_2_23_equality','--file',public.as_posix(),'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineConvex.theorem_2_23_inclusion:compiled','--dependency','lean:BanditRL.OnlineConvex.binary_subgradient_decomposition:compiled','--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Actual post-comment sequential root/Tests bound; task-only candidate, whole Goal ACTIVE.')
