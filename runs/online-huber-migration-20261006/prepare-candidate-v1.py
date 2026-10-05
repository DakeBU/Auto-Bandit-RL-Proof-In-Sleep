"""Record the exact Huber candidate after sequential combined root/Tests builds."""
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
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineHuber.lean')
assert load(run/'body-binding-audit-v1.json')['status']=='passed'
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineHuber.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
for p,h in dict(freeze['canary'],**freeze['root_Tests']).items():assert sha(p)==h,p
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(label+'.log')).read_text(encoding='utf-8'));assert m,label
 jobs[label]=int(m.group(1))
assert load(run/'Tests-v1-01-exit.json')['started_at']>=load(run/'root-v1-01-exit.json')['ended_at']
ready=load(run/'ready-dependencies-v1.json');assert sha(ready['graph_path'])==ready['graph_sha256']
write('compiled-dependencies-v1.json',dict(status='fresh-scoped-compiled-environment-graph-with-unchanged-mathematical-tokens',**{k:ready[k] for k in ['graph_path','graph_sha256','nodes','proof_nodes','definition_nodes','edges','required_proof_value_pairs','actual_project_value_pairs','full_graph_export','canary_graph_export']},qualified_module_only_comment_delta=True,current_code_tokens_identical=True,fresh_root_Tests_jobs=jobs,root_Tests_sequential=True,teaching_edges_are_not_proof_dependencies=True,edge_boundary='Direct type/value references include definitions, not all theorem-to-theorem pairs or full/canary export.'))
ob=load(run/'proof-obligations-proving-v1.json');ob['stage']='candidate'
for row in ob['required']:row['state']='fresh-body-and-combined-Lean-passed-package-gates-pending'
write('proof-obligations-candidate-v1.json',ob)
digest='ONE Example2.15/19retainedproofs3full definitions/0newmathcode,nodes. Source-implicit delta>=0 including0, actual CompleteHilbert/sourcefiniteEuclidean, deterministicstreams/source stockillustration/featurebeforeprediction-labelafter. Actual seam calculus/vectorgradient/globalConvex/projectionidentity/RegularLoss producers feed same causal shared fixedeta endpoint retaining negative residual for allT>=0, T0cancellation/delta0/Z0admitted. Positive knownhorizon coefficient1 eta_T=1/sqrtT averagebound; numericenvelopeTendsto0 versusliteral actual one-sided eventualaverage<epsilon for eachfixedu/nonuniformcutoff/separaterunfamily, no signedconvergence/anytime/Chapter4. Whole14canaries/36unique named standard3-or-noneaxes/no sorryAx/19guards, actual22nodes2954directreferences includingdefs notfull/canary export. Distinct CONTRACT/BODY accepted-with-explicit-delta, eight readerqualifications applied; root/Tests sequentialactualsuccess. Fullharness/contributor/site/registry/finalreader/PR pending. Legacy11beforepackage→10onlyOnlineHuberafteracceptance, Chapter1migration/Chapter2null/incomplete/wholeGoalACTIVE; globalSGB/main/live unchanged. Nativegates and prompt/fileconventions distinct, threeactorsrequestedAstra/medium nohuman/external/runtimeattestation. Read-only retrieval/currentenvironment fresh; globalreference-index rewrite notrun.'
write('memory-digest-candidate-v1.md',digest)
write('retrieval-index-candidate-v1.md','Exact19nativeheaders/completecontexts/3full definitions in online-huber-migration-v1; actual36@types/whole14canary seam/vector/trueupdate/residual/tunedaverage/eventual tests. Pinned seamHasDerivWithin/innerSLchainrule/Monotone.convexOn_univ_of_deriv/sqrtinverse APIs, actualglobalRegularLoss/fullspaceprojection/sharedtheorem_2_13_fixed. Current scoped22nodes2954directtype/valueedges/18localproofpairs+sharedfixedOGDpair; singlelowerretainedroute, zero newgenericdeclarations/imports/dependencyupgrades. Sourceblind/currentcontract/bodyreceipts/historyrawsnapshots; sourcequalified oneprintedexample/19supportproofs. Globalreference-indexrefreshnotrun; Chapter2/Book incomplete, finalgatespending.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write('candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=19,retained_definitions=3,new_proofs=0,frozen_headers=freeze['headers'],fresh_jobs=jobs,remaining_gates=['fullharness','contributor','site/registry/finalreader','raw/PR'],source_terminal_accepted=False,chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only Example2.15 retained Huber/one-sided average candidate, Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'huber_average_eventually'),'--declaration','BanditRL.OnlineHuber.huber_average_eventually','--file',public.as_posix(),'--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineHuber.huber_average_bound:compiled','--dependency','lean:BanditRL.OnlineHuber.huber_rate_tendsto:compiled','--dependency','lean:BanditRL.OnlineHuber.huber_regret_fixed:compiled','--dependency','lean:BanditRL.OnlineGradientDescent.theorem_2_13_fixed:compiled','--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Exact Huber candidate/sequentialrootTests/task-only frontier recorded; full package acceptance pending.')
