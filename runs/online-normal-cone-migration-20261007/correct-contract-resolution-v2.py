"""Correct only resolution metadata for exact reviewed globals after native appends."""
from common import *
old=load(RUN/'prior-contract-binding-v1.json');preserved=load(RUN/'historical-raw-supersession-contract-v1.json')
snap={(str(Path(r['path']).resolve()),r['raw_sha256']):r['snapshot'] for r in preserved['rows']}
mutable={str(Path(p).resolve()) for p in ['runs/lifecycle_sessions.jsonl','runs/trials.jsonl']};rows=[]
for r in old['rows']:
 p=r['path'];expected=r['sha256'];canonical=str(Path(p).resolve())
 resolved=snap[(canonical,expected)] if canonical in mutable else r['resolved']
 assert sha(resolved)==expected,(p,resolved)
 rows.append(dict(path=p,sha256=expected,resolved=resolved))
write(RUN/'prior-contract-binding-v2.json',dict(status='passed-exact-reviewed-raw-resolution',rows=rows,report_sha256=old['report_sha256'],supersedes_resolution_metadata_only='prior-contract-binding-v1.json',old_v1_raw_sha256=sha(RUN/'prior-contract-binding-v1.json'),original_receipt_report_and_snapshots_unmodified=True,corrected_paths=['runs/lifecycle_sessions.jsonl','runs/trials.jsonl'],reason='v1 capture-time matching-current paths became stale after correctly appended native events; v2 points to exact immutable reviewed prefix snapshots.',mathematical_repairs=[]))
fixed();print('Versioned resolution-only correction: all',len(rows),'contract bindings now point to exact reviewed bytes, old v1 preserved.')
