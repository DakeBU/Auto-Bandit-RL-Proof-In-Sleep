"""Accept only the two reviewed terminals; the real whole-book Goal stays active."""
from pathlib import Path
import json,hashlib,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-FINITE-LOSS-20261005'
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
    p=run/n;assert not p.exists(),p
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
allrows=[]
for name in ['source-contract-receipt-v1.json','public-body-receipt-v1.json','final-reader-receipt-v1.json']:
    r=load(run/name);assert r['actor']['task']=='/root/source_reviewer'
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta']
    assert not r.get('mathematical_repairs',r.get('required_repairs',[]))
    assert sha(r['report'])==r['report_sha256']
    for row in r['reviewed_files']:assert sha(row['path'])==row['sha256'],row['path'];allrows.append(row)
    if name=='final-reader-receipt-v1.json':
        reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
        for row in load(run/'final-reader-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
for gate_name in ['root-v1-01','Tests-v1-01','full-harness-v2-01','contributor-exact-v3-01','scoped-diff-v2-01',
                  'site-build-v3','site-check-v3','registry-v3-01','browser-v3-01','candidate-frontier-shadow-v1']:
    assert load(run/(gate_name+'-exit.json'))['exit_code']==0,gate_name
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineConstraintFiniteLoss.lean')
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
write('accepted-binding-audit-v1.json',dict(status='passed',raw_review_rows=len(allrows),reviewed_inputs_rechecked=True,
    frozen_headers=freeze['headers'],prior_final_history_bindings='history-binding-audit-v3.json',
    prior_accepted_reports_receipts_unmodified=True))
write('accepted-decision-v1.json',dict(status='accepted-with-explicit-delta',scope='two new finite-loss/domain proofs only',
    primary_terminal='BanditRL.OnlineConvex.finite_add_indicator_iff',supporting_terminal='BanditRL.OnlineConvex.effectiveDomain_add_indicator',
    source='Orabona v10 unnumbered finite-loss necessity, explicitly refined to iff; domain helper separately hypothesized',
    frozen_headers=freeze['headers'],new_public_proofs=2,public_canary_proofs=8,named_standard_axiom_audits=10,
    new_registry_nodes=2,old_registry_IDs_URLs_preserved=10804,root_jobs=9088,Tests_jobs=9230,full_tests=466,existing_skips=7,
    site_source_commit=load(run/'registry-v3.json')['source_commit'],stacked_base='f6daaa68927398df9fd8b756f3ac2dd28247c1e7',
    final_review_receipt='final-reader-receipt-v1.json',final_review_report_sha256=r['report_sha256'],
    compiled_scope_graph='compiled-dependency-graph-v1.json',full_graph_export=False,main_relative_gate='failed16legacy-contract-migrations',
    chapter_mandatory_total=None,chapter_complete=False,goal_complete=False,PR_delivery_pending=True,merged=False,live=False,
    failure_record_paths=['private-probe-repair-v2.json','canary-proof-repair-v2.json','axiom-parser-repair-v2.json','full-harness-repair-v1.json',
        'contributor-schema-repair-v2.json','scoped-diff-audit-v2.json','site-route-schema-repair-v2.json','site-featured-schema-repair-v3.json']))
write('accepted-obligations-v1.json',dict(required=[dict(name=n,statement_hash=h,state='accepted-scoped') for n,h in freeze['headers'].items()],
    mandatory_source_consequence_closed='finite constrained loss implies membership, with exact iff refinement',
    supporting_foundation_closed='effective-domain intersection under global noBottom',
    remaining_chapter_legacy_migrations=19,chapter_total=None,Chapter2_complete=False,future_chapters='3-16 unenumerated mandatory',goal_complete=False))
write('source-inventory-acceptance-overlay-v1.json',dict(base_inventory='docs/contracts/online-book-v1/source-inventory.json',base_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'),
    additive_only=True,source_anchor='Section2.1.1 printed9-10/PDF21-22 unnumbered finite-loss constraint sentence',
    accepted_public_names=['BanditRL.OnlineConvex.'+n for n in freeze['headers']],delta='Source necessity refined to exact iff; separately hypothesized domain helper.',chapter_complete=False,goal_complete=False))
write('contribution-acceptance-overlay-v1.json',dict(manifest='research-wiki/contribution-contracts/online-finite-loss-20261005.json',manifest_sha256=sha('research-wiki/contribution-contracts/online-finite-loss-20261005.json'),
    source_contract='source-contract-receipt-v1.json',body='public-body-receipt-v1.json',reader='final-reader-receipt-v1.json',
    integrated='integrated-gates-overlay-v2.json',accepted_decision='accepted-decision-v1.json',semantic_status='accepted-with-explicit-delta',
    earlier_candidate_pending_fields_superseded_additively=True,chapter_complete=False,goal_complete=False))
write('memory-digest-accepted-v1.md','Two genuine finite-loss/domain terminals accepted with explicit source necessity-to-iff/arbitrary-carrier/noBottom distinctions; eight canaries/ten named standard3 axioms/two guards/current scoped2node121edge compiled graph. Fresh root9088/Tests9230/full466/7, exact stacked contributor5paths/1manifest, clean site/unique2nodes+10804oldIDsURLs and actual browser first viewport passed. All failures/repairs/raw original bindings preserved; no statement weakening. Chapter2 incomplete/totalnull/19legacy migrations, whole Chapters1-16 real Goal active. Mainrelative16missing production contracts, stacked draft PR pending, no merge/live/retirement.')
write('retrieval-index-accepted-v1.md','Accepted decision/binding/obligations/overlays here. Source/header contracts docs/contracts/online-finite-loss-v1. Public OnlineConstraintFiniteLoss.lean/Tests.OnlineConstraintFiniteLossCanary/shared root; source/body/final reader distinct receipts and hashes; all failed versions preserved. Current compiled graph in compiled-dependency-graph-v1.json; same canonical shared registry2new/10804inherited. WholeBook/Chapter2 incomplete; next source/migration leaf needs its own contract.')
gate('accepted-reviewer-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','reviewer','--kind','review','--status','accepted',
    '--run-id',run.name,'--notes','Only two fixed finite-loss/domain endpoints accepted after distinct final source/reader review and integrated gates; Chapter2/book incomplete.',
    '--verifier-evidence',str(run/'final-reader-receipt-v1.json'),'--harness','hierarchical','--progress-class','terminal','--reviewer-validated')
trials=[json.loads(line) for line in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if line.strip()]
write('accepted-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('accepted-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','accepted','--payload-json',
    json.dumps(dict(run_id=run.name,accepted_decision=str(run/'accepted-decision-v1.json'),new_proofs=2,chapter_complete=False,goal_complete=False,merged=False,live=False)))
gate('accepted-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; two finite-loss terminals accepted only, Chapter2/book incomplete',
    '--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'finite_add_indicator_iff'),'--declaration','BanditRL.OnlineConvex.finite_add_indicator_iff','--file',str(public),
    '--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:BanditRL.OnlineConvex.extendedIndicator:compiled',
    '--dependency','review:source-reader:accepted','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--output',str(run/'accepted-frontier-v1.json'),'--shadow-status','pending')
gate('accepted-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-accepted-v1.md'),'--frontier',str(run/'accepted-frontier-v1.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Scoped two-terminal acceptance recorded; whole runtime Goal remains ACTIVE; PR delivery pending.')
