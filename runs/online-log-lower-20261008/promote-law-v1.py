from common_v1 import *
fixed()
assert load(RUN/'law-attempt-v2-exit.json')['exit_code']==0
assert PUBLIC.read_bytes()==(RUN/'snapshots/public-first-leaf-v1.lean.raw').read_bytes()
source=PUBLIC.read_text(encoding='utf-8');ending='end BanditRL.OnlineLearning.GuessingLower'
addition=(RUN/'law-addition-v2.lean.txt').read_text(encoding='utf-8')
PUBLIC.write_bytes((source[:source.rindex(ending)]+addition+'\n'+ending+'\n').encode('utf-8'))
write(RUN/'snapshots/public-law-v1.lean.raw',PUBLIC.read_bytes())
gate('public-law-build-v1','lake','build','BanditRLProof.OnlineGuessingLogLower')
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,normalize_statement
headers=load(CONTRACT/'planned-public-headers-v1.json')
for name in list(headers)[:7]:
    assert lean_declaration_header(PUBLIC,name)==normalize_statement(headers[name]),name
write(RUN/'law-progress-v1.json',dict(
    compiled_frozen_targets=list(headers)[:7], auxiliary_proofs=['sum_vectors_succ'],
    actual_definition_sha256=sha(CONTRACT/'planned-definitions-v1.lean.txt'),
    public_sha256=sha(PUBLIC), remaining_frozen_targets=list(headers)[7:],
    native_global_frontier_unchanged=True, source_lower_terminal_closed=False,
    source_package_accepted=False,BODY_review='pending',chapter_complete=False,goal_complete=False))
fixed()
print('Seven exact frozen public proofs plus one finite-history decomposition compiled; nine required targets remain.')
