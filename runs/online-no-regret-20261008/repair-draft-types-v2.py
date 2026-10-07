from common_v1 import *
fixed();assert load(RUN/'draft-proposition-identities-v1-exit.json')['exit_code']==1
lines=(RUN/'draft-proposition-identities-v1.lean').read_text(encoding='utf8').splitlines()
imports=list(dict.fromkeys(s for s in lines if s.startswith('import ')))
write(RUN/'draft-proposition-identities-v2.lean','\n'.join(imports+['']+[s for s in lines if not s.startswith('import ')]))
write(RUN/'draft-type-preparation-repair-v2.json',dict(failed='draft-proposition-identities-v1',reason='Combined independently typed contexts inserted a second import block after declarations.',repair='Versioned verification file hoists unchanged imports to the beginning; all statement/model bytes and source-blind packet unchanged.',no_target_proof_or_statement_change=True))
gate('draft-proposition-identities-v2','lake','env','lean',RUN/'draft-proposition-identities-v2.lean')
write(RUN/'draft-type-verification-v2.json',dict(status='twelve proposed closed proposition identities elaborated',targets_sha256=sha(CONTRACT/'targets-v1.json'),neutral_sha256=sha(RUN/'neutral-packet-v1.lean'),type_identity_source_sha256=sha(RUN/'draft-proposition-identities-v2.lean'),actual_public_target_proofs_begun=False,compiled_type_identities_not_target_proofs=True,new_theorem_bodies=0))
fixed()
