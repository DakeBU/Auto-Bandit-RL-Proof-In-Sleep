"""Retain original payload; append actual publication-byte repair before its own review."""
from common_v1 import *
passed('committed-raw-audit-v3-01');p=load(RUN/'pr-payload-v1.json')
note='Publication-byte repair: original delivery/audit1/diagnostic1/audit2 failures are retained. The later actual raw mismatch was CRLF-to-LF Git conversion; only this RUN now uses local * -text attributes and scoped renormalization to preserve unchanged bound raw bytes. The original missing-dictionary trace remains unreproduced, with no invented cause; the effective explicit-head/full-tree audit verifies every current RUN raw file against actual Git blobs. Separate metadata review and fresh final publication audit are required; source/public/reader/FINAL evidence and exactly one native accepted trial remain unchanged.'
p['body']=p['body'].rstrip()+'\n\n'+note+'\n';write(RUN/'pr-body-v2.md',p['body']);write(RUN/'pr-payload-v2.json',p)
write(RUN/'pr-payload-before-API-v2.json',dict(path=(RUN/'pr-payload-v2.json').as_posix(),sha256=sha(RUN/'pr-payload-v2.json'),original_v1_payload_preserved=True,before_first_API_use=True,metadata_review_pending=True))
print('Original draft payload preserved; version2 includes actual raw-byte publication repair.')
