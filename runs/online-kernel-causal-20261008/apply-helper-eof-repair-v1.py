from common_body_v1 import *
import ast

fixed_integrated()
assert sha(RUN/'helper-eof-receipt-v1.json') == '4f0ac37c6227ecc7a7c1905ddb34d43df150a893844c6b9b783671fdeb753928'
assert sha(RUN/'helper-eof-review-v1.md') == '5f424253452dcc0b1ab586a84ac93d7a61e10a56d4133d34d85004789191ac5e'
r = load(RUN/'helper-eof-receipt-v1.json')
assert r['verdict'] == 'accepted' and r['inputs_unchanged'] and r['fixed_input_count'] == 22
rows = load(RUN/'helper-eof-review-inputs-v1.json')['rows']
assert all(sha(x['path']) == x['sha256'] for x in rows)
proposal = load(RUN/'helper-eof-repair-proposal-v1.json')
p = Path(proposal['exact_mutable_path'])
old = Path(proposal['old_snapshot']).read_bytes()
new = Path(proposal['proposed_snapshot']).read_bytes()
assert p.read_bytes() == old == new+b'\n'
assert ast.dump(ast.parse(old)) == ast.dump(ast.parse(new))
write(RUN/'helper-eof-repair-authority-v1.json',dict(
    receipt_sha256=sha(RUN/'helper-eof-receipt-v1.json'),report_sha256=sha(RUN/'helper-eof-review-v1.md'),
    exact_mutable_path=p.as_posix(),old_sha256=proposal['old_sha256'],new_sha256=proposal['proposed_new_sha256'],
    original_snapshot=proposal['old_snapshot'],new_snapshot=proposal['proposed_snapshot'],
    actual_reviewed_count=22,original_body350_receipt_sha256=sha(RUN/'public-body-receipt-v1.json'),
    AST_unchanged=True,production_Test_statement_proof_pin_changes=0,goal_complete=False))
guard = (RUN/'common_body_v1.py').read_text(encoding='utf8')
needle = '''        if p.as_posix() in snapshots:
'''
assert guard.count(needle) == 1
addition = '''        if p.resolve() == (RUN/'common_canary_v1.py').resolve():
            repair = load(RUN/'helper-eof-repair-authority-v1.json')
            assert sha(RUN/'helper-eof-receipt-v1.json') == repair['receipt_sha256']
            assert sha(RUN/'helper-eof-review-v1.md') == repair['report_sha256']
            rr = load(RUN/'helper-eof-receipt-v1.json')
            assert rr['verdict'] == 'accepted' and rr['inputs_unchanged'] and rr['fixed_input_count'] == 22
            assert sha(repair['original_snapshot']) == row['sha256'] == repair['old_sha256']
            assert sha(repair['new_snapshot']) == repair['new_sha256'] == sha(p)
            assert Path(repair['original_snapshot']).read_bytes() == p.read_bytes()+b'\\n'
            continue
'''
write(RUN/'common_body_v2.py',guard.replace(needle,addition+needle))
commit = (RUN/'commit_owned_v1.py').read_text(encoding='utf8').replace('from common_body_v1 import *','from common_body_v2 import *')
write(RUN/'commit_owned_v2.py',commit)
candidate = (RUN/'prepare-candidate-commit-v1.py').read_text(encoding='utf8')
candidate = candidate.replace('from commit_owned_v1 import *','from commit_owned_v2 import *').replace('-v1','-v2')
needle = "bound.update(x['sha256'] for x in load(RUN/'draft-baseline-v1.json')['rows'])"
assert needle in candidate
candidate = candidate.replace(needle,needle+"\nbound.update(x['sha256'] for x in load(RUN/'helper-eof-review-inputs-v1.json')['rows'])")
write(RUN/'prepare-candidate-commit-v2.py',candidate)
p.write_bytes(new)
from common_body_v2 import fixed_integrated as repaired_fixed
repaired_fixed()
write(RUN/'helper-eof-applied-v1.json',dict(actual_old_sha256=hashlib.sha256(old).hexdigest(),actual_new_sha256=sha(p),
    exact_one_final_LF_removed=True,AST_unchanged=True,original_raw_snapshot_retained=True,
    original_body350_review_not_rewritten=True,separate22_repair_bound=True,
    candidate_v1_failure_retained=True,production_Test_reader_pin_changes=0,goal_complete=False))
print('Exact reviewed EOF-only repair applied; strict v2 guard binds old350 snapshot plus22 repair. No proof changes.',flush=True)
