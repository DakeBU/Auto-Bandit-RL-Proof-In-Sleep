from common_v1 import *
fixed()
old = RUN/'typed-api-search-v1.lean'
write(RUN/'typed-api-search-v2.lean',old.read_text(encoding='utf8').replace(
    'Filter.tendsto_natCast_atTop_atTop','tendsto_natCast_atTop_atTop'))
write(RUN/'api-repair-v2.json',dict(error='Incorrect namespace Filter for actual root tendsto_natCast_atTop_atTop',
    prior_raw_log_sha256=sha(RUN/'typed-api-search-v1.log'),target_or_proof_changed=False,
    source_definition_or_toolchain_changed=False,repair='API query namespace only'))
gate('typed-api-search-v2','lake','env','lean',RUN/'typed-api-search-v2.lean')
gate('draft-public-target-types-v1','lake','env','lean',CONTRACT/'public-context-v1.lean')
gate('draft-neutral-target-types-v1','lake','env','lean',CONTRACT/'neutral-context-v1.lean')
fixed()
