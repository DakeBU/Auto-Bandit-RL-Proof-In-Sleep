from common_body_v1 import *

fixed_integrated()
trials = [json.loads(line) for line in (ROOT/'runs/trials.jsonl').read_text(encoding='utf8').splitlines() if line.strip()]
own = [t for t in trials if t.get('task') == TASK]
assert len(own) == 12
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t,ensure_ascii=False) for t in own))
write(RUN/'memory-digest-shadow-v1.md','Task: `'+TASK+'`\n\n'+
    (RUN/'memory-digest-candidate-v1.md').read_text(encoding='utf8')+
    '\nDistinct actual BODY350 accepted-with-explicit-delta. Exact R1-R7 and combined/site/FINAL/native/delivery gates remain separately required. No global SGB frontier or lifecycle memory mutation.\n')
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective',
    'Persistent Orabona Chapters1-16; five derived behavioral-kernel causal producers; whole program still required',
    '--leaf',TASK,'--kind','review','--statement',
    'Five frozen causal-kernel bodies and stochastic feedback canary compiled; same selected process all-horizon expected-fixed terminal. Combined/site/FINAL/native acceptance pending.',
    '--file',RUN/'public-body-review-v1.md','--source-status','source-reviewed','--leaf-status','gate-pending',
    '--dependency','review:source-body:accepted',
    '--dependency','lean:BanditRL.OnlineLearning.causal_kernel_realization_and_expectedFixed_excess:compiled',
    '--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl',
    '--memory-digest',RUN/'memory-digest-shadow-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
report = load(RUN/'candidate-frontier-shadow-v1.log')
write(RUN/'candidate-shadow-audit-v1.json',dict(actual_trial_rows=len(own),
    actual_report=report,global_frontier_memory_unchanged=True,
    command_exit_only_not_sufficient=True,package_accepted=False,chapter_complete=False,goal_complete=False))
assert report['mismatches'] == [], report['mismatches']
fixed_integrated()
print('Own scoped shadow actual12 trial rows and zero mismatches; global frontier/memory unchanged.',flush=True)
