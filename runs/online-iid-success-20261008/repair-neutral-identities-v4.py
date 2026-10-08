from common_v1 import *
fixed()
prior = (RUN/'neutral-identities-v2.lean').read_text(encoding='utf8')
assert prior.count('universe u v w z')==1
write(RUN/'neutral-identities-v4.lean',prior.replace('universe u v w z\n',''))
gate('neutral-identities-v4','lake','env','lean',RUN/'neutral-identities-v4.lean')
write(RUN/'neutral-identity-receipt-v4.json',dict(neutral_whole_prop_identities=4,
    definition_identities=3,actual_exit=0,semantic_target_proofs=0,
    retained_failed_logs={n:sha(RUN/(n+'.log')) for n in
        ['neutral-identities-v1','neutral-identities-v2','neutral-type-diagnosis-v3']},
    diagnosis='Explicit shared universe instances fixed Prop rfl; duplicate global universe command in concatenated audit independently failed parse/elaboration',
    repair='Remove only duplicate universe command from concatenated audit; all public/neutral headers unchanged',
    public_context_sha256=sha(CONTRACT/'public-context-v1.lean'),
    neutral_context_sha256=sha(CONTRACT/'neutral-context-v1.lean')))
fixed()
