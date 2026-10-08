from common_integrated_v2 import *
from commit_owned_v2 import stage_owned, commit_owned

fixed_integrated()
assert load(RUN/'reader-context-repair-v3.json')['public_sha256']==sha(PUBLIC)
stage_owned()
gate('current-reader-scoped-diff-v3',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','reader-v3')
commit_owned('Match each private-seed proof note to its exact hypotheses')
gate('contributor-current-reader-v3',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
log=(RUN/'contributor-current-reader-v3.log').read_text(encoding='utf8')
assert 'affected production paths: 5' in log and 'changed contribution contracts: 1' in log
assert 'Contributor contract passed.' in log
write(RUN/'current-reader-gate-bindings-v3.json',dict(actual_source_commit=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip(),
    actual_contributor_receipt='contributor-current-reader-v3-exit.json',affected_production_paths=5,
    current_own_reader_headers_are_specific=True,applicable_Lean_by_complete_unchanged_body_and_pin_hashes=True,
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    site_pixels_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False))
stage_owned()
gate('current-reader-evidence-scoped-diff-v3',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','reader-evidence-v3')
commit_owned('Bind current source-qualified reader to contributor and Lean gates')
fixed_integrated()
print('Fresh reader contributor gate passed; clean current head:',subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip())
