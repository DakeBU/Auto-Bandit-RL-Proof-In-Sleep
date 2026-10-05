"""Record the two compiled terminals without claiming chapter or book acceptance."""
from pathlib import Path
import json,hashlib,subprocess,sys,re
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-FINITE-LOSS-20261005'
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
    p=Path(p);assert not p.exists(),p
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
receipts=['source-contract-receipt-v1.json','public-body-receipt-v1.json'];rows=[]
for name in receipts:
    r=load(run/name);assert r['actor']['task']=='/root/source_reviewer'
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['mathematical_repairs']
    assert sha(r['report'])==r['report_sha256']
    for row in r['reviewed_files']:assert sha(row['path'])==row['sha256'],row['path'];rows.append(row)
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=len(rows),receipts=receipts))
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
    assert load(run/(label+'-exit.json'))['exit_code']==0
    m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(label+'.log')).read_text(encoding='utf-8'));assert m,label
    jobs[label]=int(m.group(1))
freeze=load(run/'draft-freeze-v1.json');names=['BanditRL.OnlineConvex.'+n for n in freeze['headers']]
public='BanditRLProof/OnlineConstraintFiniteLoss.lean'
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(Path(public),n).encode()).hexdigest()==h
manifest=load('research-wiki/contribution-contracts/online-convex-migration-20261005.json')
manifest.update(id=task,frontier_cell='online-convex',target='Close the mandatory unnumbered finite constrained loss consequence with an exact finite-real iff and separate noBottom effective-domain intersection.',
    affected_files=[public,'Tests/OnlineConstraintFiniteLossCanary.lean','BanditRLProof.lean','Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json'],declarations=names)
manifest['source']['anchor']='Section2.1.1 unnumbered finite-loss constraint sentence, printed9-10/PDF21-22; exact iff is explicit refinement, separate domain helper is not a numbered printed theorem.'
manifest['reuse_plan']=dict(classification='missing',decision='new_shared',
    searched_existing=['Actual public declaration search and semantic EReal/indicator/domain retrieval; two new exact endpoints absent.',
        'Pinned add_top_of_ne_bot/coe_ne_top/coe_ne_bot/coe_toReal actual type probe.'],
    reused_declarations=['BanditRL.OnlineConvex.effectiveDomain','BanditRL.OnlineConvex.extendedIndicator','EReal.add_top_of_ne_bot'],
    new_shared_declarations=names,known_consumers=['Tests.OnlineConstraintFiniteLossCanary'],
    planned_consumers=['Source OCO prediction finite-loss feasibility via the finite criterion','Source comparator finite-loss feasibility via the same finite criterion','Constrained-loss effective-domain analysis under noBottom'],
    no_duplicate_wrapper=True,decision_reason='One shared pointwise criterion serves learner and comparator; domain helper retains its own necessary hypothesis. No duplicate per-Book tree or fake wrapper.')
manifest['semantic_roundtrip'].update(status='accepted',verdict='accepted-with-explicit-delta',
    remaining_semantic_delta='Distinct source-contract/body actors verified necessity-to-iff refinement, arbitrary carrier generalization, ordinary EReal addition and separate global noBottom. Reader/integrated/package review still pending; no human/external/runtime model attestation.')
manifest['graph_contribution'].update(lean_graph='new-node',focus_targets=names,
    functor_reason='Routine source constraint algebra; no conceptual cross-setting functor claim.',
    visual_review='Current scoped compiled graph two nodes/121 actual direct edges; shared reader/registry/site gate pending.')
manifest['progress_updates'].update(teaching_route='updated: existing online-convex route extended by two canonical source-qualified endpoints; all other Book subtrees retained.',
    results_ledger='no-change-with-reason: additive finite-loss acceptance overlay only after gates; original source inventory immutable.',
    roadmap='no-change-with-reason: Chapter2 incomplete/mandatory totalnull, whole Goal active, global SGB untouched.')
manifest['truth_boundary']='Two genuine new proofs/eight public canaries. Exact finite-real iff permits both infinities without noBottom; below-top domain identity separately retains global noBottom. Necessary source direction refined explicitly; arbitrary carrier generalizes Rd. Ordinary addition retained; counterexample to dropping noBottom public. This is not completion of Chapter 2 or Chapters1-16. Legacy/source enumeration remains mandatory; stacked PR/local compilation do not update main/live.'
manifest['verification'].update(focused_checks=['Actual focused root/module/canary build, ten named standard3 axiom outputs, two native guards, unchanged frozen headers and fresh scoped compiled proof-term graph.'],
    bandit_check='Fresh explicit root/Tests passed; full harness pending.',site_build='Fresh applicable full Lean gate required before clean lean-verified build.',site_check='Two new canonical nodes/old IDsURLs/source-qualified reader checks pending.')
write('research-wiki/contribution-contracts/online-finite-loss-20261005.json',manifest)
for n,h in freeze['headers'].items():
    gate('compiled-trial-'+n+'-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','lower','--kind','build','--status','compiled',
        '--run-id',run.name,'--lean',public,'--statement-hash',h,'--changed-file',public,'--new-declaration','BanditRL.OnlineConvex.'+n,
        '--verifier-evidence',str(run/'focused-v2-01.log'),'--harness','hierarchical','--progress-class','compiled-leaf',
        '--notes','Exact source-stabilized public body/axioms/canaries verified; distinct body review accepted-with-explicit-delta. Full package pending.')
write(run/'memory-digest-candidate-v1.md','Two fixed terminals genuinely closed in Lean; no assumed finite/domain conclusion. Finite iff no hbot; domain identity global hbot. Eight canaries/ten standard3 axioms/two guards/current scoped2node121edge proof-term graph actual. Distinct contract/body review accepted-with-explicit-delta. Parser/coercion/evidence-parser failures preserved with unchanged terminal hashes. Fresh root/Tests passed; full harness/reader/registry/site/contributor/raw/package/PR pending. Whole Goal active/Chapter2 totalnull/global SGB unchanged.')
write(run/'retrieval-index-candidate-v1.md','Source/headers:docs/contracts/online-finite-loss-v1. Public:OnlineConstraintFiniteLoss.lean/finite_add_indicator_iff/effectiveDomain_add_indicator. External canary:Tests.OnlineConstraintFiniteLossCanary. Actual pinned EReal retrieval logs; ten named axioms; current scoped compiled dependencies; distinct source/body receipts. Original probes/failures preserved. Same shared Book route/root/registry, no new project.')
trials=[json.loads(line) for line in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if line.strip()]
write(run/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('candidate-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,new_proofs=2,canary_proofs=8,frozen_headers=freeze['headers'],fresh_jobs=jobs,remaining_gates=['full harness','site/registry/reader','contributor/raw/PR'],chapter_complete=False,goal_complete=False)))
gate('candidate-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; only two finite-loss terminals candidate, Chapter2/book incomplete',
    '--leaf',task,'--kind','lean','--statement',lean_declaration_header(Path(public),'finite_add_indicator_iff'),'--declaration',names[0],'--file',public,
    '--source-status','source-body-reviewed','--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineConvex.extendedIndicator:compiled',
    '--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--output',str(run/'candidate-frontier-v1.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'candidate-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v1.md'),'--frontier',str(run/'candidate-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Actual candidate/root/Tests/manifest/task-local frontier recorded; full package pending.')
