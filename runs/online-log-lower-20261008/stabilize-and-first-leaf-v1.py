from common_v1 import *

fixed()
receipt = load(RUN/'source-contract-receipt-v1.json')
assert receipt['actor']['task'] == '/root/source_reviewer'
assert receipt['verdict'] == 'accepted-with-explicit-delta'
assert sha(receipt['report']) == receipt['report_sha256']
assert sha(RUN/'source-contract-receipt-v1.json') == 'e89c703f34f87adc95c4ca333a2bdf45e0ce4d487617dd6436774bfa29767fe9'
for key in ['required_repairs','required_mathematical_repairs','required_metadata_repairs']:
    assert not receipt[key], key
reviewed = {x['path']: x['sha256'] for x in receipt['reviewed_files']}
inputs = load(RUN/'source-contract-inputs-v2.json')
assert len(inputs['rows']) == receipt['fixed_input_count'] == 153
for row in inputs['rows']:
    assert sha(row['path']) == reviewed[row['path']] == row['sha256'], row['path']
for path, expected in reviewed.items():
    assert sha(path) == expected, path
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import normalize_statement
headers = load(CONTRACT/'planned-public-headers-v1.json')
fingerprints = load(CONTRACT/'planned-statement-fingerprints-v1.json')
for name, header in headers.items():
    assert hashlib.sha256(normalize_statement(header).encode()).hexdigest() == fingerprints[name], name
write(RUN/'stabilized-contract-v1.json', dict(
    status=receipt['verdict'], contract_version=1, verified_fixed_rows=153,
    receipt_bindings=len(reviewed), report_sha256=receipt['report_sha256'],
    receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),
    planned_public_proofs=16, planned_model_definitions=8,
    first_ready_leaf=PRE+'probability_mem',
    terminal='randomized_log_lower with one fixed binary vector outside seed integral',
    required_reader_corrections=receipt['required_reader_corrections'],
    proof_bodies_present=False, source_package_accepted=False,
    chapter_complete=False, goal_complete=False))
native('stabilized-event-v1','lifecycle-event','--session',TASK,'--event','stabilized',
       '--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,
       stabilized_contract=(RUN/'stabilized-contract-v1.json').as_posix(),
       source_package_accepted=False,chapter_complete=False,goal_complete=False)))
native('proving-event-v1','lifecycle-event','--session',TASK,'--event','proving',
       '--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,
       dependency_ready_leaf=PRE+'probability_mem',
       source_package_accepted=False,chapter_complete=False,goal_complete=False)))
definitions = (CONTRACT/'planned-definitions-v1.lean.txt').read_text(encoding='utf-8')
ending = 'end BanditRL.OnlineLearning.GuessingLower'
assert definitions.rstrip().endswith(ending)
body = ''' := by
  have hc : (h.count true : ℝ) ≤ (h.length : ℝ) := by
    exact_mod_cast (List.count_le_length (a := true) (l := h))
  have hd : (0 : ℝ) < (h.length : ℝ) + 2 := by positivity
  change 0 < ((h.count true : ℝ) + 1) / ((h.length : ℝ) + 2) ∧
    ((h.count true : ℝ) + 1) / ((h.length : ℝ) + 2) < 1
  constructor
  · exact div_pos (by positivity) hd
  · exact (div_lt_one hd).mpr (by linarith)
'''
write(PUBLIC, definitions[:definitions.rindex(ending)] +
      headers['probability_mem'] + body + '\n'+ending+'\n')
write(RUN/'snapshots/public-first-leaf-v1.lean.raw', PUBLIC.read_bytes())
write(RUN/'30_lower-ready-leaf-v1.md',
      'Root staged lower worker, one route: derive actual count ≤ length, positive denominator and numerator, and strict upper bound. Exactly frozen probability_mem header. Eight reviewed model definitions and one actual theorem body; no stubs for the remaining fifteen targets. This is reusable law foundation growth, not logarithmic source-claim or chapter closure.')
gate('first-probability-build-v1','lake','build','BanditRLProof.OnlineGuessingLogLower')
fixed()
print('CONTRACT stabilized and first actual proof built; other fifteen frozen terminals unproved.')
