from common_v1 import *
fixed()
assert load(RUN/'public-law-build-v1-exit.json')['exit_code']==1
write(RUN/'law-promotion-repair-v2.json',dict(
    failed_public_sha256=sha(PUBLIC), failed_snapshot=(RUN/'snapshots/public-law-v1.lean.raw').as_posix(),
    failed_build_log_sha256=sha(RUN/'public-law-build-v1.log'),
    cause='The proof-local measure lambda annotation was applied globally in the separate addition text, accidentally annotating the vector successor sum at T rather than T+1. The independently compiled full law-v2 leaf has the correct annotation.',
    correction='Promote exactly the actually compiled full law-v2 leaf bytes, rather than the separately transformed addition.',
    frozen_headers_or_definitions_changed=False, failed_artifacts_preserved=True,
    public_build_v1_failed_not_accepted=True))
assert load(RUN/'law-attempt-v2-exit.json')['exit_code']==0
PUBLIC.write_bytes((RUN/'leaves/law-v2.lean').read_bytes())
write(RUN/'snapshots/public-law-v2.lean.raw',PUBLIC.read_bytes())
gate('public-law-build-v2','lake','build','BanditRLProof.OnlineGuessingLogLower')
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,normalize_statement
headers=load(CONTRACT/'planned-public-headers-v1.json')
for n in list(headers)[:7]:assert lean_declaration_header(PUBLIC,n)==normalize_statement(headers[n]),n
write(RUN/'law-progress-v2.json',dict(compiled_frozen_targets=list(headers)[:7],
    auxiliary_proofs=['sum_vectors_succ'],public_sha256=sha(PUBLIC),
    remaining_frozen_targets=list(headers)[7:],BODY_review='pending',
    source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed()
print('Public law-v2 actual build passed; failed first promotion retained separately.')
