from common_body_v1 import *
from tools.check_contributor_contract import validate_contract
body_fixed(True)
before=load(MANIFEST)
assert before['graph_contribution']['lean_graph']=='updated'
write(RUN/'snapshots/schema2-manifest-before-enum-repair-v1.raw',MANIFEST.read_bytes())
old_sha=sha(MANIFEST)
after=json.loads(json.dumps(before))
after['graph_contribution']['lean_graph']='integration-node'
MANIFEST.write_bytes((json.dumps(after,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
data,errors=validate_contract(MANIFEST.resolve())
write(RUN/'schema2-BODY-validation-v2.json',dict(errors=errors,
    failed_validation='schema2-BODY-validation-v1.json',repair='Use the actual schema enum integration-node instead of unsupported updated for lean_graph.',
    exact_changed_field='graph_contribution.lean_graph',before_sha256=old_sha,after_sha256=sha(MANIFEST),
    observed_outer_exit_v1=1,outer_raw_stderr_v1_saved=False,actual_schema_error_saved=True,
    public_or_canary_or_frozen_contract_changed=False,FINAL_pending=True,chapter_complete=False,goal_complete=False))
assert not errors,errors
fixed_integrated()
print('Exact schema enum repaired; active schema2 validates, all frozen mathematics unchanged.',flush=True)
