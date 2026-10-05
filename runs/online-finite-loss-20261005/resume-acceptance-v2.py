"""Repair missing native attempt binding; do not overwrite accepted mathematical artifacts."""
from pathlib import Path
import json,hashlib,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-FINITE-LOSS-20261005';attempt='FINITE-LOSS-TWO-BODIES-V1'
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
    p=run/n;assert not p.exists(),p
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
        else:json.dump(x,f,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
assert load(run/'record-acceptance-v1-01-exit.json')['exit_code']==1
assert '--reviewer-validated requires the reviewed --attempt-id' in (run/'accepted-reviewer-trial-v1.log').read_text(encoding='utf-8')
for name in ['source-contract-receipt-v1.json','public-body-receipt-v1.json','final-reader-receipt-v1.json']:
    r=load(run/name);assert sha(r['report'])==r['report_sha256']
    for row in r['reviewed_files']:assert sha(row['path'])==row['sha256'],row['path']
decision=load(run/'accepted-decision-v1.json');public=Path('BanditRLProof/OnlineConstraintFiniteLoss.lean')
for n,h in decision['frozen_headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
write('native-attempt-binding-repair-v2.json',dict(failed_step='accepted-reviewer-trial-v1',failed_acceptance_command='record-acceptance-v1-01',
    repair='Assign the actual already compiled two-body proof bundle a named native attempt and bind its reviewer record; no mathematical acceptance input/decision overwritten.',
    attempt_id=attempt,retrospective_evidence_binding=True,new_compilation_claim=False,proof_or_statement_change=False,
    immutable_decision_sha256=sha(run/'accepted-decision-v1.json')))
gate('compiled-attempt-binding-v2',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','lower','--kind','build','--status','compiled',
    '--run-id',run.name,'--attempt-id',attempt,'--lean',str(public),'--statement-hash',decision['frozen_headers']['finite_add_indicator_iff'],
    '--verifier-evidence',str(run/'focused-v2-01.log'),'--verifier-evidence',str(run/'named-axioms-v1-01.log'),'--harness','hierarchical',
    '--new-declaration',decision['primary_terminal'],'--new-declaration',decision['supporting_terminal'],
    '--progress-class','compiled-leaf','--obligations-before','2','--obligations-after','0',
    '--notes','Retrospective named binding of actual two-body attempt and its existing compilation evidence, not another compile or benchmark run.')
gate('accepted-reviewer-trial-v2',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','reviewer','--kind','review','--status','accepted',
    '--run-id',run.name,'--attempt-id',attempt,'--reviewer-validated','--verifier-evidence',str(run/'final-reader-receipt-v1.json'),
    '--harness','hierarchical','--progress-class','terminal','--obligations-before','2','--obligations-after','0',
    '--notes','Two fixed terminals accepted by distinct final reviewer; precise native attempt binding added after flag validation failure. Chapter/book incomplete.')
trials=[json.loads(line) for line in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if line.strip()]
write('accepted-scoped-trials-v2.jsonl','\n'.join(json.dumps(t) for t in trials if t.get('task')==task))
gate('accepted-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','accepted','--payload-json',json.dumps(dict(run_id=run.name,
    accepted_decision=str(run/'accepted-decision-v1.json'),native_attempt=attempt,new_proofs=2,chapter_complete=False,goal_complete=False,merged=False,live=False)))
gate('accepted-frontier-refresh-v2',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; two finite-loss terminals accepted only, Chapter2/book incomplete',
    '--leaf',task,'--kind','lean','--statement',lean_declaration_header(public,'finite_add_indicator_iff'),'--declaration',decision['primary_terminal'],'--file',str(public),
    '--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:BanditRL.OnlineConvex.extendedIndicator:compiled',
    '--dependency','review:source-reader:accepted','--trials',str(run/'accepted-scoped-trials-v2.jsonl'),'--output',str(run/'accepted-frontier-v2.json'),'--shadow-status','pending')
gate('accepted-frontier-shadow-v2',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'accepted-scoped-trials-v2.jsonl'),
    '--memory-digest',str(run/'memory-digest-accepted-v1.md'),'--frontier',str(run/'accepted-frontier-v2.json'))
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
write('native-acceptance-overlay-v2.json',dict(status='passed',accepted_decision='accepted-decision-v1.json',accepted_decision_sha256=sha(run/'accepted-decision-v1.json'),
    repaired_native_attempt=attempt,frontier='accepted-frontier-v2.json',shadow_gate='accepted-frontier-shadow-v2',chapter_complete=False,goal_complete=False))
print('Named native binding/lifecycle/frontier/shadow repaired and passed; immutable mathematical decision unchanged.')
