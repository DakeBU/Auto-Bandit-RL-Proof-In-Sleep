from common_integrated_v2 import *

fixed_integrated()
m=load(MANIFEST)
assert m['semantic_roundtrip']['status']=='source-reviewed'
write(RUN/'snapshots'/'schema2-source-reviewed-before-BODY-acceptance-v2.raw',MANIFEST.read_bytes())
m['semantic_roundtrip']['status']='accepted'
m['semantic_roundtrip']['remaining_semantic_delta']+=' Bounded CONTRACT/BODY semantic acceptance only; reader/FINAL/native package acceptance remains pending.'
MANIFEST.write_bytes((json.dumps(m,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
sys.path.insert(0,str(ROOT))
from tools.check_contributor_contract import validate_contract
parsed,errors=validate_contract(MANIFEST.resolve())
write(RUN/'schema2-BODY-semantic-validation-v2.json',dict(actual_checker='tools.check_contributor_contract.validate_contract',
    errors=errors,manifest_sha256=sha(MANIFEST),BODY_receipt_sha256=sha(RUN/'public-body-receipt-v2.json'),
    semantic_status='accepted for bounded CONTRACT/BODY only',
    committed_diff_gate_ran=False,package_accepted=False,chapter_complete=False,goal_complete=False))
assert parsed is not None and not errors,errors
fixed_integrated()
print('Native schema2 validation passed; committed production diff and FINAL/package acceptance still pending.')
