"""Keep final qualified source/reader raw bytes portable without changing their identities."""
from common import *
fixed(True)
paths=[PUBLIC.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json','research-wiki/contribution-contracts/online-subgradient-absolute-migration-20261007.json','runs/lifecycle_sessions.jsonl','runs/trials.jsonl']
rows=[]
for p in paths:
 dest=RUN/('snapshots/final-qualified-'+p.replace('/','--')+'.txt');write(dest,Path(p).read_bytes());assert sha(dest)==sha(p)
 rows.append(dict(path=p,raw_sha256=sha(p),snapshot=dest.as_posix(),snapshot_sha256=sha(dest),authorized_delta='Exact final qualified local raw source/reader/native bytes retained for later authorized changes and line-ending-independent historical resolution; no reserialization.'))
write(RUN/'historical-raw-supersession-final-source-v1.json',dict(rows=rows,status='exact-current-raw-final-source-preserved',raw_hash_boundary='LF/CRLF/mixed bytes bind exact snapshots, not JSON reserialization or automatic other-host recertification.'))
print('Exact final qualified public/reader/manifest/native raw snapshots retained; canonical bytes unchanged.')
