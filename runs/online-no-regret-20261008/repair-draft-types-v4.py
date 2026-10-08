from common_v1 import *
fixed();assert load(RUN/'draft-proposition-identities-v3-exit.json')['exit_code']==1
s=(RUN/'draft-proposition-identities-v3.lean').read_text(encoding='utf8')
for n in [1,2,3,11,12]:
 old='NeutralPacket.B%03d = A%03d'%(n,n);new='NeutralPacket.B%03d.{v} = A%03d.{v}'%(n,n)
 assert old in s;s=s.replace(old,new)
write(RUN/'draft-proposition-identities-v4.lean',s)
write(RUN/'draft-universe-audit-v4.json',dict(actual_root_cause='Closed polymorphic Prop constants are instantiated at independent fresh universe parameters unless explicitly pinned; merely declaring the same universe variable does not force both constants to use it.',repair='Explicitly instantiate both sides of B001/B002/B003/B011/B012 equalities at the same arbitrary universe v. Other real-only propositions remain unchanged.',supersedes='v3 attribution to implicit Pi binders alone was incomplete; actual v3 diagnostics show independent universe levels. All public/neutral/source targets remain exact.',no_carrier_restriction=True,no_statement_or_source_change=True,no_target_proof_begun=True))
gate('draft-proposition-identities-v4','lake','env','lean',RUN/'draft-proposition-identities-v4.lean')
write(RUN/'draft-type-verification-v4.json',dict(status='twelve actual proposed closed proposition equalities compiled',actual_public_target_proofs_begun=False,new_theorem_bodies=0,type_equality_evidence_only=True,proof_mode='B001–B003 explicit propext/Pi conversion with shared arbitrary universe; other nine rfl, B011/B012 same explicit universe',targets_sha256=sha(CONTRACT/'targets-v1.json'),neutral_sha256=sha(RUN/'neutral-packet-v1.lean'),verification_source_sha256=sha(RUN/'draft-proposition-identities-v4.lean')))
fixed()
