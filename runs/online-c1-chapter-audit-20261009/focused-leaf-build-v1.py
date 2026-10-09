from common_v1 import *
fixed()
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header
label=sys.argv[1]
module=ROOT/'BanditRLProof/OnlineFTLInitializationRegret.lean'
snapshot=RUN/'leaves'/(label+'.lean.txt')
write(snapshot,module.read_bytes())
checked=[]
for t in load(CONTRACT/'general-initialization-targets-stabilized-v3.json')['new_targets']:
    if ('theorem '+t['name'].rsplit('.',1)[-1]+' ') not in module.read_text('utf8'):continue
    header=lean_declaration_header(module,t['name'])
    assert hashlib.sha256(header.encode('utf8')).hexdigest()==t['statement_hash'],t['id']
    checked.append(dict(id=t['id'],name=t['name'],actual_statement_hash=t['statement_hash']))
rc=gate(label,'lake','build','BanditRLProof.OnlineFTLInitializationRegret',required=False)
fixed()
write(RUN/'leaves'/(label+'-attempt.json'),dict(actual_exit=rc,source_snapshot=snapshot.as_posix(),source_sha256=sha(snapshot),frozen_headers=checked,phase='focused proof attempt only',chapter_complete=False,goal_complete=False))
raise SystemExit(rc)
