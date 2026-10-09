from publication_guard_v1 import *
fixed()
p=RUN/'integrated-candidate-v1.py'
old='from canary_driver import native_snapshot\n'
new='''def native_snapshot(label):
    ps=[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md','trials.jsonl']]
    write(RUN/(label+'.json'),dict(rows=[dict(path=p.as_posix(),exists=p.exists(),sha256=sha(p) if p.exists() else None,before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii') if p.exists() else None) for p in ps]))
'''
s=p.read_text(encoding='utf8');assert s.count(old)==1
write(RUN/'integrated-candidate-v2.py',s.replace(old,new))
for label in ['candidate-wrapper-repair-before-v2']:
    ps=[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md']]
    write(RUN/(label+'.json'),dict(rows=[dict(path=p.as_posix(),sha256=sha(p),before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in ps]))
event('candidate-wrapper-repair-v2','repair',dict(task=TASK,failure='Old prepublication guard imported transitively after exact reviewed publication',change='Local exact native snapshot function; keep unchanged publication_guard and all frozen math/approved five deltas',statement_changed=False,definitions_changed=False,proof_changed=False))
print('Versioned wrapper repair prepared; original failed script retained.',flush=True)
