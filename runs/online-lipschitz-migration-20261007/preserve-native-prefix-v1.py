"""Preserve exact reviewed native log bytes, including cryptographically verified append-only prefixes."""
from common_v2 import *
stage=sys.argv[1];receipt={'contract':'source-contract-receipt-v1.json','body':'public-body-receipt-v1.json','final':'final-reader-receipt-v1.json'}[stage]
r=load(RUN/receipt);reviewed={row['path']:row['sha256'] for row in r['reviewed_files']};rows=[]
for p in ['runs/lifecycle_sessions.jsonl','runs/trials.jsonl']:
 expected=reviewed[p];raw=Path(p).read_bytes();h=hashlib.sha256();end=0;matched=None
 for line in raw.splitlines(keepends=True):
  h.update(line);end+=len(line)
  if h.hexdigest()==expected:matched=raw[:end];break
 assert matched is not None,('Reviewed raw bytes are not an exact native append-only prefix',p,expected)
 dest=RUN/('snapshots/'+stage+'-reviewed-'+p.replace('/','--')+'.txt');write(dest,matched);assert sha(dest)==expected
 rows.append(dict(path=p,raw_sha256=expected,snapshot=dest.as_posix(),snapshot_sha256=sha(dest),authorized_delta='Native task events/trials appended only; original reviewed raw prefix cryptographically verified, never reserialized or edited.'))
write(RUN/('historical-raw-supersession-'+stage+'-v1.json'),dict(rows=rows,status='exact-reviewed-native-prefix-preserved',receipt=receipt,all_source_math_unchanged=True))
if stage=='contract':
 resolved={row['path']:row['snapshot'] for row in rows};bindings=[]
 for row in r['reviewed_files']:
  p=row['path'];q=resolved[p] if p in resolved else p;assert sha(q)==row['sha256'];bindings.append(dict(path=p,sha256=row['sha256'],resolved=q))
 write(RUN/'prior-contract-binding-v1.json',dict(status='passed',rows=bindings,report_sha256=r['report_sha256'],original_receipt_unmodified=True,only_native_append_only_changes=True))
print(stage,'native reviewed raw bytes preserved; no statement/proofbody repair.')
