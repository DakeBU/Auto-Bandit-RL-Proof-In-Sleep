"""Save exact FINAL-reviewed native prefixes before any accepted trial/event."""
from common_v4 import *
r=load(RUN/'final-reader-receipt-v1.json');reviewed={x['path']:x['sha256'] for x in r['reviewed_files']};rows=[]
for p in ['runs/lifecycle_sessions.jsonl','runs/trials.jsonl']:
 raw=Path(p).read_bytes();h=hashlib.sha256();end=0;matched=None
 for line in raw.splitlines(keepends=True):
  h.update(line);end+=len(line)
  if h.hexdigest()==reviewed[p]:matched=raw[:end];break
 assert matched is not None,(p,reviewed[p])
 dest=RUN/('snapshots/final-reviewed-'+p.replace('/','--')+'.txt');write(dest,matched);assert sha(dest)==reviewed[p]
 rows.append(dict(path=p,raw_sha256=reviewed[p],snapshot=dest.as_posix()))
write(RUN/'historical-raw-supersession-final-v1.json',dict(status='passed',rows=rows,original_reviewed_native_bytes_preserved=True))
print('Exact FINAL reviewed native prefixes preserved for additive acceptance events.')
