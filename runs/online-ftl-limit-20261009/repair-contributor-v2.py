from common_body_v1 import *

integrated_fixed()
r=load(RUN/'final-reader-receipt-v1.json')
assert r['verdict']=='rejected' and r['inputs_unchanged']
assert r['report_sha256']==sha(RUN/'final-reader-review-v1.md')
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert head==load(ROOT/'tmp/online-ftl-limit-candidate-head-v1.json')['actual_head']
write(RUN/'FINAL-M1-repair-v2.json',dict(original_verdict='rejected',
    original_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),
    cause='Contributor checker compares BASE..HEAD; precommit staged checks did not cover this package. Stack check was N/A, main check omitted new module.',
    repair='Rerun both contributor bases against the actual candidate HEAD and require explicit coverage of new production module.',
    actual_candidate_head=head,mathematical_contract_unchanged=True,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    old_NA_failure_and_rejection_preserved=True,package_accepted=False,goal_complete=False))
for label,base in [('candidate-contributor-stack-v2',BASE),('candidate-contributor-main-v2','origin/main')]:
    gate(label,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base)
    log=(RUN/(label+'.log')).read_text(encoding='utf8')
    assert 'Contributor contract passed.' in log and 'N/A' not in log
    assert ' - covered: '+PUBLIC.relative_to(ROOT).as_posix() in log
    assert 'changed paths: 0\n' not in log
write(RUN/'contributor-repair-gates-v2.json',dict(actual_head=head,
    both_nonempty_bases_cover_new_production_module=True,
    receipts=['candidate-contributor-stack-v2-exit.json','candidate-contributor-main-v2-exit.json'],
    mathematical_contract_unchanged=True,distinct_repair_review_pending=True,package_accepted=False))
integrated_fixed()
print('Both actual candidate HEAD gates explicitly cover the new production module; distinct repair FINAL required.',flush=True)
