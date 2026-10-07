from common_v1 import *
fixed();assert load(RUN/'draft-proposition-identities-v2-exit.json')['exit_code']==1
s=(RUN/'draft-proposition-identities-v2.lean').read_text(encoding='utf8')
assert s.count('universe v\n')==2
first=s.index('universe v\n');second=s.index('universe v\n',first+1)
s=s[:second]+s[second:].replace('universe v\n','',1)
for n in [1,2,3]:
 old='example : NeutralPacket.B%03d = A%03d := by rfl'%(n,n)
 new='''example : NeutralPacket.B%03d = A%03d := by
  apply propext
  constructor
  · intro h X V f p
    exact h X V f p
  · intro h X V f p
    exact @h X V f p'''%(n,n)
 assert old in s;s=s.replace(old,new)
write(RUN/'draft-proposition-identities-v3.lean',s)
write(RUN/'draft-type-audit-v3.json',dict(previous_failures=['v1 import block placement','v2 duplicate universe declaration and implicit carrier binders in first three header-closed types'],representation_audit='One shared declared universe, unchanged mathematical source/context/propositions, explicit propext forward/backward carrier applications for B001–B003 instead of requiring rfl over implicit vs explicit Pi binders.',public_and_neutral_targets_unchanged=True,no_target_proof_begun=True))
gate('draft-proposition-identities-v3','lake','env','lean',RUN/'draft-proposition-identities-v3.lean')
write(RUN/'draft-type-verification-v3.json',dict(status='twelve actual proposed closed proposition equalities compiled',actual_public_target_proofs_begun=False,new_theorem_bodies=0,type_equality_evidence_only=True,proof_mode='B001–B003 explicit propext/Pi conversion; other nine rfl',targets_sha256=sha(CONTRACT/'targets-v1.json'),neutral_sha256=sha(RUN/'neutral-packet-v1.lean'),verification_source_sha256=sha(RUN/'draft-proposition-identities-v3.lean')))
fixed()
