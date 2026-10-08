from common_body_v2 import *

fixed_integrated()
trials = [json.loads(line) for line in (ROOT / 'runs/trials.jsonl').read_text(
    encoding='utf8').splitlines() if line.strip()]
own = [t for t in trials if t.get('task') == TASK]
assert len(own) == 6
write(RUN / 'candidate-scoped-trials-v1.jsonl', '\n'.join(
    json.dumps(t, ensure_ascii=False) for t in own))
write(RUN / 'memory-digest-shadow-v1.md', 'Task: `' + TASK + '`\n\n' +
      (RUN / 'memory-digest-candidate-v1.md').read_text(encoding='utf8') +
      '\nDistinct actual BODY285 accepted-with-explicit-delta; exact R1-R7, four frozen public bodies and canary unchanged. Combined/reader/FINAL/native gates remain separately required.\n')
native('candidate-frontier-refresh-v1', 'frontier-refresh', '--root-objective',
       'Persistent Orabona Chapters1-16; four derived ambient-completion causal producers; whole program required',
       '--leaf', TASK, '--kind', 'review', '--statement',
       'Four frozen completed-information bodies compiled, actual original-process expected fixed excess and completed-but-not-ordinary positive-variance canary; combined/reader/FINAL/native acceptance pending.',
       '--file', RUN / 'public-body-review-v1.md', '--source-status',
       'source-reviewed', '--leaf-status', 'gate-pending', '--dependency',
       'review:source-body:accepted', '--dependency',
       'lean:BanditRL.OnlineLearning.completed_predictable_private_seed_expectedFixed_excess:compiled',
       '--trials', RUN / 'candidate-scoped-trials-v1.jsonl', '--output',
       RUN / 'candidate-frontier-v1.json', '--shadow-status', 'pending')
native('candidate-frontier-shadow-v1', 'frontier-shadow', '--trials',
       RUN / 'candidate-scoped-trials-v1.jsonl', '--memory-digest',
       RUN / 'memory-digest-shadow-v1.md', '--frontier',
       RUN / 'candidate-frontier-v1.json')
fixed_integrated()
