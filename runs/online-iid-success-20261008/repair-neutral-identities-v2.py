from common_v1 import *
fixed()
prior = (RUN/'neutral-identities-v1.lean').read_text(encoding='utf8')
text = prior.replace('S002 = Q002','S002.{u, v} = Q002.{u, v}').replace(
    'S003 = Q003','S003.{u} = Q003.{u}').replace('S004 = Q004','S004.{u} = Q004.{u}')
write(RUN/'neutral-identities-v2.lean',text)
gate('neutral-identities-v2','lake','env','lean',RUN/'neutral-identities-v2.lean')
write(RUN/'neutral-identity-receipt-v2.json',dict(neutral_whole_prop_identities=4,
    definition_identities=3,actual_exit=0,semantic_target_proofs=0,
    original_failure_sha256=sha(RUN/'neutral-identities-v1.log'),
    repair='Explicit matching universe instantiations in identity audit; public/neutral draft headers unchanged',
    public_context_sha256=sha(CONTRACT/'public-context-v1.lean'),
    neutral_context_sha256=sha(CONTRACT/'neutral-context-v1.lean')))
fixed()
