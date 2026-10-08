from common_integrated_v1 import *
fixed_integrated()
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf8').splitlines() if s.strip()]
trials=[t for t in trials if t.get('task')==TASK]
assert len(trials)==3
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t,ensure_ascii=False) for t in trials))
write(RUN/'memory-digest-candidate-v2.md','Task: `'+TASK+'`\n\n'+
    (RUN/'memory-digest-candidate-v1.md').read_text(encoding='utf8')+
    '\nThis digest names only the own audit task. Twelve old proofs/zero new public proofs; source audit count5 remains pending. '
    'Public prefix/variance/history proof bytes and exact twelve signatures remain frozen. BODY185/CONTRACT93 accepted with deltas; original history reused, not human/external review. '
    'Whole16 Goal, source16/null, universal model and chapter obligations remain required.\n')
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective',
    'Persistent Orabona Chapters1-16; five source core audits only, zero new production proofs',
    '--leaf',TASK,'--kind','review','--statement',
    'Five existing core source-module audits with twelve exact frozen public declarations; full headers/original proof values and legacy pointwise/global-bound deltas preserved. FINAL/native source audit gate pending, new production proofs=0.',
    '--file',RUN/'public-body-review-v1.md','--source-status','source-reviewed','--leaf-status','gate-pending',
    '--dependency','review:source-body:accepted',
    '--dependency','lean:'+PRE+'iid_meanPredict_excess:compiled',
    '--dependency','lean:'+PRE+'history_policy_loss_ge_variance:compiled',
    '--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl',
    '--memory-digest',RUN/'memory-digest-candidate-v2.md','--frontier',RUN/'candidate-frontier-v1.json')
fixed_integrated()
print('Actual own source-audit candidate shadow passed; global SGB unchanged, five audits still pending FINAL/native.')
