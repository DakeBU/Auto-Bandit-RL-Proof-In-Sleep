from common import *
s=(RUN/'record-acceptance-v5.py').read_text(encoding='utf-8')
s=s.replace("history=load(RUN/'history-binding-audit-v3.json');snap={(r['path'],r['raw_sha256']):r['resolved_raw_file'] for r in history['rows']}", "history=load(RUN/'history-binding-audit-v3.json');snap={(str(Path(r['path']).resolve()),r['raw_sha256']):r['resolved_raw_file'] for r in history['rows']}\nfor row in load(RUN/'historical-raw-supersession-final-v2.json')['rows']:\n assert sha(row['snapshot'])==row['raw_sha256'];snap[(str(Path(row['path']).resolve()),row['raw_sha256'])]=row['snapshot']\nappend_paths={str(Path(p).resolve()) for p in ['runs/lifecycle_sessions.jsonl','runs/trials.jsonl']}")
s=s.replace("resolved=p if sha(p)==h else snap[(p,h)];", "resolved=p if sha(p)==h and str(Path(p).resolve()) not in append_paths else snap[(str(Path(p).resolve()),h)];")
write(RUN/'record-acceptance-v6.py',s)
generated('acceptance-append-prefix-helper-before-use-v6.json',[RUN/'record-acceptance-v6.py'])
print('Future acceptance bindings resolve append-only logs to exact reviewed snapshots before native appends; not yet executed.')
