from pathlib import Path
import json, hashlib, sys, subprocess
root = Path.cwd()
run = Path(__file__).resolve().parent
sys.path.insert(0, str(root / 'tools'))
import abrl_lifecycle as lifecycle
headers = json.loads((run / 'draft-headers-v1.json').read_text(encoding='utf-8'))
freeze = json.loads((run / 'draft-freeze.json').read_text(encoding='utf-8'))
body = run / 'leaves/body-06.lean'
assert json.loads((run / 'body-06-exit.json').read_text(encoding='utf-8'))['exit_code'] == 0
context = (run / 'leaves/context-v1.lean.txt').read_text(encoding='utf-8').split('end BanditRL.OnlineUnitScaling')[0]
assert body.read_text(encoding='utf-8').startswith(context)
for name in headers:
    assert lifecycle.statement_hash(lifecycle.lean_declaration_header(body, name)) == freeze['headers'][name]
public = root / 'BanditRLProof/OnlineUnitScaling.lean'
assert not public.exists()
public.write_bytes(body.read_bytes())
with (root / 'BanditRLProof.lean').open('a', encoding='utf-8', newline='\n') as f:
    f.write('import BanditRLProof.OnlineUnitScaling\n')
attempts=[]
for label,count in [('body-01',2),('body-02',6),('body-03',11),('body-04',12),('body-05',22),('body-06',22)]:
    command=json.loads((run / (label+'-exit.json')).read_text(encoding='utf-8'))
    attempts.append({'attempt':label,'target_prefix_count':count,'actual_exit':command['exit_code'],
        'elapsed_seconds':command['elapsed_seconds'],'leaf':str((run/'leaves'/(label+'.lean')).relative_to(root)).replace('\\','/'),
        'compiled':command['exit_code']==0, 'public_package_acceptance':False})
with (run/'leaf-attempts.jsonl').open('w',encoding='utf-8',newline='\n') as f:
    for row in attempts:f.write(json.dumps(row,ensure_ascii=False)+'\n')
obligations=json.loads((run/'proof-obligations.json').read_text(encoding='utf-8'))
obligations['stage']='proving-public-compilation-pending'
for row in obligations['required']:row['state']='compiled-leaf-not-public-accepted'
obligations['remaining_gates']=['focused public build','named lookup/canary/axioms','distinct body review','rootTests/fullharness','native graph','Book/site/reader/immutableaudit','scoped stackedPR']
with (run/'proving-obligations-v1.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(obligations,f,ensure_ascii=False,indent=2);f.write('\n')
(run/'body-repair-05.md').write_text(
    'Attempt body-05 failed at regret_scaling: native rewrite did not match the beta-redex current-loss application. Exact target/error is retained in body-05.log and actual exit1 in body-05-exit.json. Source/header/context and route unchanged. Body-06 explicitly beta-reduces with dsimp only then applies the fully instantiated already-proved loss_value_scaling; it compiles all22 real bodies. Removed two redundant unreachable ring tactics; all frozen statements unchanged. The runner had separately failed printing Unicode to GBK after it already captured raw Lean output/exit; subsequent invocation uses python -X utf8 without changing the source-reviewed runner. Nonfatal unused-section/hypothesis warnings retained; no premise removal. No failed output is marked compiled. Earlier readonly nonexistent-path/help-choice probes did not mutate targets; actual CLI is trial-log, not record-trial.\n',encoding='utf-8')
runner=[sys.executable,'-X','utf8',str(run/'run-command.py')]
subprocess.run(runner+['lower-body-native-trial',sys.executable,'tools/bandit.py','trial-log','--task','ONLINE-UNIT-SCALING-20261004','--run-id',run.name,'--role','lower','--kind','proof','--status','compiled','--notes','Actual22 frozen bodies compile in body-06; true shared history/scaledfeedback/wrong effective schedule/regret/retainednegative terminal closed. Public compilation/canary/bodyreview/fullgates pending. body-05 beta-redex failure preserved.','--lean',str(body.relative_to(root)),'--source','ORABONA-V10-P21-22-UNIT-SCALING','--changed-file','BanditRLProof/OnlineUnitScaling.lean','--attempt-id','ONLINE-UNIT-LEAF22-BODY06','--progress-class','compiled-leaf','--obligations-before','22','--obligations-after','0','--verifier-evidence',str((run/'body-06-exit.json').relative_to(root))],check=True)
print('Published exact22 frozen bodies; combined acceptance pending.')
