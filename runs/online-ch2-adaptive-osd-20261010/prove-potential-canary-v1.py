from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
review_path = RUN/'potential-BODY-and-canary-CONTRACT-review-v1.json'
review = load(review_path)
assert sha(review_path) == '1bc6eace1631d6f76da48da8a3aae22dbe41ea3945064b8932e8b311f1fd5af7'
assert review['BODY_verdict'] == review['canary_CONTRACT_verdict'] == 'accepted-with-explicit-delta'
assert not review['required_repairs'] and review['inputs_unchanged']
assert sha(review['report']) == review['report_sha256']
assert sha(review['input_manifest']) == review['input_manifest_sha256']
for row in review['raw_input_checks']:
    assert sha(row['path']) == row['before_sha256'] == row['expected_sha256'] == row['after_sha256']
scope = review['allowed_new_Test_scope']
for row in scope['frozen_context_and_headers']:
    assert sha(row['path']) == row['sha256']
canary = Path(scope['path'])
context, first, second = [Path(r['path']).read_bytes() for r in scope['frozen_context_and_headers']]
body1 = '''  have hw : ∀ t < 4, 0 ≤ w t := by
    intro t ht
    interval_cases t <;> norm_num [w]
  have hm : ∀ t, t + 1 < 4 → w t ≤ w (t + 1) := by
    intro t ht
    have ht3 : t < 3 := by omega
    interval_cases t <;> norm_num [w]
  have ha4 : ∀ t < 4, a t ≤ 4 := by
    intro t ht
    interval_cases t <;> norm_num [a]
  have ha3 : ∀ t < 4, a t ≤ 3 := by
    intro t ht
    interval_cases t <;> norm_num [a]
  have hb := BanditRL.OnlineAdaptivePotential.weighted_potential_sum
    a w 4 4 (by norm_num) hw hm ha4
  have hs := BanditRL.OnlineAdaptivePotential.weighted_potential_sum
    a w 3 4 (by norm_num) hw hm ha3
  refine ⟨hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [sum_range_succ, a, w]
  · norm_num [a, w]
  · calc
      _ ≤ 3 * w 3 - a 4 * w 3 := hs
      _ < 4 * w 3 - a 4 * w 3 := by norm_num [a, w]
  · rfl
  · rfl
  · norm_num [a]
'''
body2 = '''  have hbound : ∀ t < 3, signed t ≤ -2 := by
    intro t ht
    interval_cases t <;> norm_num [signed]
  have hz := BanditRL.OnlineAdaptivePotential.weighted_potential_sum
    signed (fun _ => 0) (-2) 3 (by norm_num)
    (by intro t ht; norm_num) (by intro t ht; exact le_rfl) hbound
  have ht := BanditRL.OnlineAdaptivePotential.weighted_potential_sum
    terminal (fun _ => 2) 1 1 (by norm_num)
    (by intro t ht; norm_num) (by intro t ht; exact le_rfl)
    (by intro t ht; have h : t = 0 := by omega; subst t; norm_num [terminal])
  refine ⟨hz, ht, ?_, ?_⟩
  · norm_num [sum_range_succ, terminal]
  · norm_num [terminal]
'''
write(CONTRACT/'potential-canary-stabilized-v1.json', dict(
    review_sha256=sha(review_path), frozen_context_and_headers=scope['frozen_context_and_headers'],
    lower_route='Four public applications with directly retained inequality branches; finite arithmetic for fixture premises/equalities.',
    canary_BODY='pending', parent_causal_OSD='required-draft', whole_Goal='active'))
write(canary, context+b'\n'+first+body1.encode('utf8')+b'\n'+second+body2.encode('utf8')+
    b'\nend Tests.OnlineAdaptivePotentialCanary\n')
write(RUN/'potential-canary-body-attempt-v1.lean.txt', canary.read_bytes())
header_hashes = {}
for name, data in [('leading_zero_and_stall', first), ('signed_zero_and_free_terminal', second)]:
    actual = lean_declaration_header(canary, name)
    assert statement_hash(actual) == statement_hash(data.decode('utf8'))
    header_hashes[name] = statement_hash(actual)
write(RUN/'potential-canary-body-input-v1.json', dict(
    canary_sha256=sha(canary), header_hashes=header_hashes, expected_selected_public_calls=4,
    public_production_sha256=sha(PUBLIC), combined_gate='pending'))
code, out = capture('potential-canary-focused-build-v1', 'lake', 'build',
    'Tests.OnlineAdaptivePotentialCanary', required=False)
print(out)
sys.exit(code)
