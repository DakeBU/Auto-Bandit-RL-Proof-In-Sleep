from common_proving_v1 import *
contract_bindings_fixed()
for r in load(CONTRACT/'targets-v2.json')['targets']:
    native(r['id']+'-statement-fence-v1','statement-fence','--declaration',r['name'],'--file',r['path'],
        '--output',RUN/(r['id']+'-statement-fence-v1.json'))
    native(r['id']+'-safe-verify-v1','safe-verify','--fence',RUN/(r['id']+'-statement-fence-v1.json'),
        '--lean-file',r['path'])
contract_bindings_fixed()
write(RUN/'twelve-fence-audit-v1.json',dict(targets=[r['name'] for r in load(CONTRACT/'targets-v2.json')['targets']],
    actual_fence_and_safe_verify_commands=24,all_actual_exit_codes_zero=True,
    original_proof_header_bytes_preserved=True,source_contract_receipt_sha256=RECEIPT_SHA,
    actual_compile_is_a_separate_gate=True,chapter_complete=False,goal_complete=False))
