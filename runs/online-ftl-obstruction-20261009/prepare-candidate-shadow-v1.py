from common_body_v2 import *
integrated_fixed();assert load(RUN/'combined-gates-v1.json')['actual_exit_codes']==[0,0,0]
for label,args in [('help-contributor-v1',['tools/check_contributor_contract.py','--help']),
    ('help-shadow-v1',['tools/bandit.py','frontier-shadow','--help']),
    ('help-frontier-v1',['tools/bandit.py','frontier-refresh','--help']),
    ('help-site-build-v1',['website/scripts/build_site.py','--help']),
    ('help-site-check-v1',['website/scripts/check_site.py','--help'])]:
    gate(label,sys.executable,'-B','-X','utf8',*args)
write(RUN/'candidate-shadow-memory-v1.md','Task: `'+TASK+'`\n\nFour actual proofs and11 dyadic canaries/combinedrootTestsfullharness passed; BODY390 favorable. Current committed-HEAD contributor/site/FINAL/native/delivery pending. Original16/null/remainingchapters retained; GoalACTIVE.')
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective',
    'Persistent Orabona Chapters1-16; current four bounded actualFTL reconciliation terminals only',
    '--leaf',TASK,'--kind','review','--statement',
    'Four frozen actual proofs and11 same-dyadic-FTL canaries compiled; exact all-comparator iff and ordinary fixed-zero obstruction. Currentsite/FINAL/native/delivery pending.',
    '--file',RUN/'public-body-review-v1.md','--source-status','source-reviewed','--leaf-status','gate-pending',
    '--dependency','review:source-body:accepted','--dependency','lean:BanditRL.OnlineLearning.dyadic_empiricalMean_subsequences:compiled',
    '--trials',RUN/'trials.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'trials.jsonl',
    '--memory-digest',RUN/'candidate-shadow-memory-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
shadow=load(RUN/'candidate-frontier-shadow-v1.log');assert shadow['mismatches']==[] and shadow['would_mutate']==False
write(RUN/'candidate-shadow-gate-v1.json',dict(actual_shadow=shadow,global_frontier_memory_preserved=True,
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),committed_HEAD_contributor_site_FINAL_native_delivery_pending=True,
    chapter_complete=False,goal_complete=False))
integrated_fixed()
