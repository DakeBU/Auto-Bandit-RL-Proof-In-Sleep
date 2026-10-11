from common import *
old = CONTRACT/'specialization-neutral-packet-v1.lean.txt'
assert sha(old) == 'd4fef4df520edd86bad7821699c4a723c4cfc89770640851f6e67fc71088f9a3'
actual = ROOT/'BanditRLProof/OnlineConvexExtended.lean'
body = '''def realEpigraph (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

def IsConvexExtended (f : E → EReal) : Prop := Convex ℝ (realEpigraph f)'''
import re
source = re.sub(r'/--.*?-/', '', actual.read_text(encoding='utf8'), flags=re.S)
assert all(line in source for line in body.splitlines() if line)
addition = '''
/- Exact imported predicate expansion, provided as notation context only.
It defines the already used BanditRL.OnlineConvex predicates, not new assumptions:
'''+body+'''
The ambient epigraph heights are real and cast to EReal as shown. Both EReal
infinities are allowed by this convexity predicate itself. Separate properness
and global-support premises in the certificates retain their own force.
-/
'''
write(CONTRACT/'specialization-neutral-packet-v2.lean.txt', old.read_bytes()+addition.encode('utf8'))
write(RUN/'specialization-neutral-context-repair-v2.json', dict(
    v1_packet_sha256=sha(old), v2_packet_sha256=sha(CONTRACT/'specialization-neutral-packet-v2.lean.txt'),
    copied_import_definition_sha256=sha(actual), header_changes=False,
    reason='Blind decoder requested the exact imported convex-epigraph predicate expansion. Append neutral context only; preserve all v1 bytes and all four actual headers.',
    proof_or_compile_failure=False, v1_decode_pending_expansion_retained=True))
print(sha(CONTRACT/'specialization-neutral-packet-v2.lean.txt'), flush=True)
