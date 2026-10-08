from common_integrated_v1 import *
fixed_integrated()
write(RUN/'integration-validator-environment-repair-v2.json',dict(actual_old_exit=1,
    actual_error="ModuleNotFoundError: No module named 'tools'",
    evidence='actual exec_command output, not separately captured rawstderr',
    repair='Add exactworkspace ROOT to Pythonmodule searchpath for validatorimport; no production/reader/target change or integration replay',
    reader_already_integrated_with_guard=True))
sys.path.insert(0,str(ROOT))
from tools.check_contributor_contract import validate_contract
_,errors=validate_contract(MANIFEST.resolve())
write(RUN/'schema2-BODY-validation-v2.json',dict(errors=errors,
    semantic_status='accepted boundedCONTRACT/BODYonly',FINAL_pending=True,
    chapter_complete=False,goal_complete=False))
assert not errors,errors
r=body_fixed(True)
write(RUN/'reader-integrated-bindings-v2.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    old_source_cards=13,new_source_cards=1,new_proof_notes=4,new_shared_publicnodes=4,
    oldcards_notes_preserved=True,BODY_receipt_sha256=BODY_SHA,
    original_R1_R8=r['reader_requirements'],combined_gates_pending=True,
    chapter_complete=False,goal_complete=False))
fixed_integrated()
print('Scopedintegratedreader/root/Testguard andschema2validation passed; no replayed production edit.')
