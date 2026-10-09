from common_proving_v2 import *
fixed()
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
label=sys.argv[1]
module=ROOT/'Tests/OnlineLearningChapterAuditCanary.lean'
snapshot=RUN/'leaves'/(label+'.lean.txt');write(snapshot,module.read_bytes())
targets=load(CONTRACT/'chapter-canary-targets-stabilized-v1.json')['targets']
for t in targets:assert statement_hash(lean_declaration_header(module,t['name']))==t['statement_hash'],t['id']
rc=gate(label,'lake','build','Tests.OnlineLearningChapterAuditCanary',required=False)
write(RUN/'leaves'/(label+'-attempt.json'),dict(actual_exit=rc,source_sha256=sha(snapshot),source_snapshot=snapshot.as_posix(),exact_frozen_headers=27,canonical_four_unchanged=True,phase='actual canary proof attempt only',chapter_complete=False,goal_complete=False))
fixed()
raise SystemExit(rc)
