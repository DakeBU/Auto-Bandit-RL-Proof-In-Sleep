from common_body_v1 import *
integrated_fixed()
assert load(RUN/'combined-gates-v1.json')['actual_exit_codes']==[0,0,0]
for label,args in [('help-contributor-v1',['tools/check_contributor_contract.py','--help']),
    ('help-shadow-v1',['tools/bandit.py','frontier-shadow','--help']),
    ('help-frontier-v1',['tools/bandit.py','frontier-refresh','--help'])]:
    gate(label,sys.executable,'-B','-X','utf8',*args)
stage=[PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix(),'BanditRLProof.lean','Tests.lean',
    'MANIFEST.md','runs/lifecycle_sessions.jsonl',CONTRIBUTION.relative_to(ROOT).as_posix(),
    CONTRACT.relative_to(ROOT).as_posix(),RUN.relative_to(ROOT).as_posix()]+[
    p.relative_to(ROOT).as_posix() for p in READERS]+[d+'/'+TASK+'.md' for d in ['tasks','proof-obligations','conversion-windows']]
assert not subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').strip()
gate('candidate-stage-v1','git','add',*stage)
gate('candidate-contributor-stack-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('candidate-contributor-main-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main')
write(RUN/'candidate-shadow-memory-v1.md','Task: `'+TASK+'`\n\nFiveactualbody/twelvebinarycanaryfocused+combinedrootTestsfullharness passed; distinct BODY287 favorable. Candidate site/FINAL/native/delivery required. WholeGoalACTIVE, original16/null retained.')
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective',
    'Persistent Orabona Chapters1-16; current five derived actualFTL ordinarylimit hinges only',
    '--leaf',TASK,'--kind','review','--statement','Five frozen actualFTL bodies/twelvebinarycanaries compiled; exactsignedlimits and conditionalliteral producer. Currentsite/FINAL/native/delivery acceptance pending.',
    '--file',RUN/'public-body-review-v1.md','--source-status','source-reviewed','--leaf-status','gate-pending',
    '--dependency','review:source-body:accepted','--dependency','lean:BanditRL.OnlineLearning.meanPredict_fixedRegret_limit_iff:compiled',
    '--trials',RUN/'trials.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'trials.jsonl',
    '--memory-digest',RUN/'candidate-shadow-memory-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
shadow=load(RUN/'candidate-frontier-shadow-v1.log')
assert shadow['mismatches']==[] and shadow['would_mutate']==False
write(RUN/'candidate-other-gates-v1.json',dict(both_contributor_bases_actual_exit0=True,own_shadow_actual=shadow,
    global_frontier_memory_preserved=True,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    site_FINAL_native_delivery_pending=True,chapter_complete=False,goal_complete=False))
integrated_fixed()
print('Actual contributorbothbases/ownshadow gates0; globalSGB unchanged.',flush=True)
