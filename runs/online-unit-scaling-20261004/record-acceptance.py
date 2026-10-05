"""Record package acceptance only after a distinct final review and raw binding gate."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent
task='ONLINE-UNIT-SCALING-20261004'
def load(n):return json.loads((run/n).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,v):
    with (run/n).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(v,str):f.write(v+'\n')
        else:json.dump(v,f,indent=2);f.write('\n')
def gate(label,*args):
    subprocess.run([sys.executable,'-X','utf8',str(run/'run-command-v2.py'),label,*args],check=True)
review=load('final-reader-receipt.json')
assert review['verdict']=='accepted-with-explicit-delta' and not review['required_repairs']
gate('accepted-binding-audit-01',sys.executable,'-X','utf8',str(run/'verify-accepted-bindings.py'))
audit=load('accepted-binding-audit.json');assert audit['status']=='passed'
obligations=load('proof-obligations.json')
obligations.update(stage='accepted-local',public_proofs=22,canary_theorems=30,actual_axiom_names=62,
                   package_accepted=True,chapter_accepted=False,remaining_gates=['stacked draft PR delivery'])
for row in obligations['required']:
    row.update(state='accepted-local',evidence=['public-actual-bindings.json','public-focused-01-exit.json',
              'public-body-receipt-v1.json','final-reader-receipt.json','accepted-binding-audit.json'])
write('accepted-obligations.json',obligations)
decision=dict(stage='accepted-local',source_id='C2-unit-scaling',package=task,
    public_module='BanditRLProof/OnlineUnitScaling.lean',closed_terminals=obligations['terminal'],
    public_proofs=22,public_definitions_and_alias=4,canary_theorems=30,reviewer='/root/source_reviewer',
    semantic_verdict=review['verdict'],review_report_sha256=review['report_sha256'],
    binding_audit=(run/'accepted-binding-audit.json').as_posix(),
    binding_audit_sha256=sha(run/'accepted-binding-audit.json'),raw_review_rows_verified=audit['raw_review_rows_verified'],
    source_reader_commit='70c63cac7efa59d2a892b563d8affee4266be610',
    stacked_base='c4eb0fcea94e242bc93264e6d9ba3ef7d2c4acce',source_contract_version=1,
    exact_source_sha256='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17',
    compiled_local=True,full_git_diff_check_passed=False,scoped_diff_check_passed=True,
    whitespace_exception='only task raw .log evidence; every other changed path checked',
    remaining_required=['stacked draft PR delivery','older26 production independent semantic/contribution migration',
                        'complete Chapter2 source enumeration and chapter gate',
                        'Chapters3-16 and required appendix dependencies'],
    chapter_complete=False,book_complete=False,goal_complete=False,merged=False,deployed=False,
    external_human_review=False,external_model_review=False,runtime_model_independently_verified=False)
write('accepted-decision.json',decision)
write('program-milestone.json',dict(source_id='C2-unit-scaling',status='accepted-local',
    canonical_source_inventory_historical_status='compiled-candidate; additive accepted overlay preserves reviewed bytes',
    evidence=(run/'accepted-decision.json').as_posix(),chapter_2_status='partial',chapter_2_accepted=False,
    chapter_2_mandatory_count=None,future_chapters='3-16 unenumerated and required, not zero obligations',
    whole_book_goal='active',next_required='Chapter2 full source inventory and older26 production migration',
    older26_production_migration_required=True,main_updated=False,live_updated=False))
write('contribution-acceptance-overlay.json',dict(
    manifest='research-wiki/contribution-contracts/'+task+'.json',
    manifest_sha256=sha('research-wiki/contribution-contracts/'+task+'.json'),
    preserves_candidate_manifest_raw_bytes=True,semantic_roundtrip=review['verdict'],
    actual_graph='compiled-dependencies.json',site='site-final02-check-exit.json',
    public_reader='final-reader-receipt.json',immutable_bindings='accepted-binding-audit.json',
    actual_contributor_paths=8,actual_contributor_contracts=1,
    package_status='accepted-local; draft PR delivery separate',chapter_accepted=False,book_accepted=False))
digest=('Accepted-local C2-unit-scaling only:22 frozen actual proofs and four context definitions/alias,30 actual '
        'canaries,62 named standard axioms. Actual history induction/feedback/output/regret conjugacy, effective '
        'uncompensated c²eta schedule, coarsecost and sharp negative terminal closed. Whole-space only, fixed '
        'transported exogenous policy, unchanged loss units, proper/support/played-legality premises for finite '
        'performance; abstract dimension group separately labelled. c1000 nonzero actual gradient/paths, c0/c1 '
        'and T0/T1 boundaries verified. Root9086/Tests9226/full466 tests7 skips,26 canonical registry nodes,21 '
        'actual proof-value pairs,clean site02 commit70c63 and source printed21-22/PDF33-34. Distinct neutral '
        'decoder/source/body/final reader accepted-with-explicit-delta; immutable raw audit'+str(audit['raw_review_rows_verified'])+
        ' rows. Preserve every actual proof/canary/native-kind/GBK-print/author-map/untracked-harness/exporter '
        'stackoverflow/site-route failure and repair; compact graph is the same complete graph. Full diff failed '
        'only task raw.log whitespace; scoped check covers every other path. Candidate source inventory and '
        'contribution manifest preserved through explicit accepted overlays. Draft PR pending; older26 migration '
        'and fullChapter2 inventory/gate mandatory; laterchapters unenumeratednull, wholeGoalACTIVE/globalSGB '
        'untouched. No main/live/merge/deploy/human/externalreview claim.')
write('memory-digest-accepted.md',digest)
write('retrieval-index-accepted.md',
      'Reuse shared OnlineSubgradientPolicy.history_succ/regret_fixed, OnlineHuber.fullSpace/project_fullSpace, '
      'OnlineConvex.theorem_2_28, HasFDerivAt.comp and OnlineOptimalStep.upperBound. Actual proof-value '
      'edges and source-qualified registry checked in compiled-dependencies.json and registry-final02.json; '
      'these differ from teaching navigation. Actual target/source hashes and review rows in accepted-binding-audit.json. '
      'Next chapter audit must reconcile Prop2.11/Lemma2.12 inventory with old fixedOGD exact source and '
      'independent-review production migration, without changing historical contracts or dropping unnumbered results.')
gate('accepted-reviewer-native-trial',sys.executable,'-X','utf8','tools/bandit.py','trial-log',
     '--task',task,'--run-id',run.name,'--role','reviewer','--kind','review','--status','compiled',
     '--attempt-id','ONLINE-UNIT-PUBLIC22-BODY01','--reviewer-validated','--progress-class','closed-frontier',
     '--verifier-evidence',str(run/'accepted-decision.json'),
     '--notes','Distinct final source reader and immutable raw gate accepted unit package only; actual22 public proofs/30 canaries/62axioms/rootTests/full466/7/26registry/21proof-value pairs/clean site02. Chapter2/book incomplete; stacked PR pending.')
trials=[json.loads(line) for line in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if line.strip()]
write('accepted-scoped-trials.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
leaf=load('candidate-frontier.json')['current_leaf']
gate('accepted-frontier-refresh',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh',
     '--root-objective','Persistent Orabona Chapters1-16 Goal; accepted unit scaling package only, Chapter2/book incomplete',
     '--leaf',task,'--kind','lean','--statement',leaf['statement'],'--declaration',leaf['declaration'],
     '--file',leaf['file'],'--source-status','accepted','--leaf-status','accepted',
     '--dependency','lean:BanditRL.OnlineUnitScaling.regret_scaling:compiled',
     '--dependency','lean:BanditRL.OnlineSubgradientPolicy.regret_fixed:compiled',
     '--dependency','review:final-reader:accepted','--dependency','harness:full-bandit:passed',
     '--trials',str(run/'accepted-scoped-trials.jsonl'),'--output',str(run/'accepted-frontier.json'),'--shadow-status','pending')
gate('accepted-frontier-shadow',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow',
     '--trials',str(run/'accepted-scoped-trials.jsonl'),'--memory-digest',str(run/'memory-digest-accepted.md'),
     '--frontier',str(run/'accepted-frontier.json'))
gate('accepted-lifecycle',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event',
     '--session',task,'--event','accepted','--payload-json',json.dumps(dict(run_id=run.name,
     scope='C2-unit-scaling package only',public_proofs=22,canaries=30,semantic_verdict=review['verdict'],
     immutable_raw_rows=audit['raw_review_rows_verified'],chapter_complete=False,book_complete=False,
     goal_complete=False,merged=False,deployed=False)))
print('Unit package accepted locally; whole Goal active; PR delivery still required.')
