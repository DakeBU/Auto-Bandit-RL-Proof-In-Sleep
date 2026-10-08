from common_body_v1 import *
import ast

fixed_integrated()
authority = load(RUN/'helper-eof-repair-authority-v1.json')
assert authority['receipt_sha256'] == sha(RUN/'helper-eof-receipt-v1.json') == '4f0ac37c6227ecc7a7c1905ddb34d43df150a893844c6b9b783671fdeb753928'
assert authority['report_sha256'] == sha(RUN/'helper-eof-review-v1.md') == '5f424253452dcc0b1ab586a84ac93d7a61e10a56d4133d34d85004789191ac5e'
r = load(RUN/'helper-eof-receipt-v1.json')
assert r['verdict'] == 'accepted' and r['inputs_unchanged'] and r['fixed_input_count'] == 22
assert not r['required_blocking_repairs'] and r['report_sha256'] == authority['report_sha256']
assert all(sha(x['path']) == x['sha256'] for x in load(RUN/'helper-eof-review-inputs-v1.json')['rows'])
proposal = load(RUN/'helper-eof-repair-proposal-v1.json')
p = Path(authority['exact_mutable_path'])
old = Path(authority['original_snapshot']).read_bytes()
new = Path(authority['new_snapshot']).read_bytes()
assert p.read_bytes() == old == new+b'\n'
assert sha(p) == authority['old_sha256'] == r['permitted_exact_scope']['old_sha256']
assert sha(authority['new_snapshot']) == authority['new_sha256'] == r['permitted_exact_scope']['new_sha256']
assert ast.dump(ast.parse(old)) == ast.dump(ast.parse(new))

candidate = (RUN/'prepare-candidate-commit-v1.py').read_text(encoding='utf8')
candidate = candidate.replace('from commit_owned_v1 import *','from commit_owned_v2 import *')
for label in ['candidate-RAW-Git-bindings','candidate-full-diff','candidate-diff-raw-exceptions',
              'candidate-scoped-diff','candidate-source-commit','contributor-candidate-stacked',
              'contributor-candidate-origin-main']:
    candidate = candidate.replace(label+'-v1',label+'-v2')
needle = "bound.update(x['sha256'] for x in load(RUN/'draft-baseline-v1.json')['rows'])"
assert candidate.count(needle) == 1
candidate = candidate.replace(needle,needle+"\nbound.update(x['sha256'] for x in load(RUN/'helper-eof-review-inputs-v1.json')['rows'])")
write(RUN/'prepare-candidate-commit-v2.py',candidate)
write(RUN/'helper-eof-apply-failure-v1.json',dict(
    script='apply-helper-eof-repair-v1.py',actual_tool_process_exit=1,
    failure='Assertion at candidate dependency filename lookup after overly broad version-label substitution',
    partial_files=['helper-eof-repair-authority-v1.json','common_body_v2.py','commit_owned_v2.py'],
    exact_target_unchanged_at_failure=True,old350_and22_inputs_preserved=True,
    resolution='New resume version uses only explicit output-label substitutions; dependencies remain v1.'))
p.write_bytes(new)
from common_body_v2 import fixed_integrated as repaired_fixed
repaired_fixed()
write(RUN/'helper-eof-applied-v1.json',dict(actual_old_sha256=hashlib.sha256(old).hexdigest(),actual_new_sha256=sha(p),
    exact_one_final_LF_removed=True,AST_unchanged=True,original_raw_snapshot_retained=True,
    original_body350_review_not_rewritten=True,separate22_repair_bound=True,
    candidate_v1_failure_retained=True,production_Test_reader_pin_changes=0,goal_complete=False))
print('Exact reviewed one-byte EOF repair applied; strict v2 guard passed.',flush=True)
