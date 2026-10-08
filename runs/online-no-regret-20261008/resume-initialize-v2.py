from common_v1 import *
assert load(RUN/'native-new-task-v1-exit.json')['exit_code']==0
assert load(RUN/'native-conversion-window-v1-exit.json')['exit_code']==1
write(RUN/'conversion-scaffold-repair-v2.json',dict(failure='native-conversion-window-v1',reason='new-task already creates the conversion window; explicit second creation correctly refuses overwrite.',repair='Preserve native scaffold bytes, then fill this new task-owned scaffold; skip duplicate creation.',source_or_terminal_changed=False))
for folder in ['tasks','conversion-windows','proof-obligations']:
 p=Path(folder)/(TASK+'.md');write(RUN/'snapshots'/('native-scaffold-'+folder+'--'+TASK+'.raw'),p.read_bytes())
s=(RUN/'initialize-v1.py').read_text(encoding='utf8');s=s[s.index("native('draft-lifecycle-v1'"):]
exec(compile(s,'initialize-v1-tail-after-scaffold-repair','exec'))
