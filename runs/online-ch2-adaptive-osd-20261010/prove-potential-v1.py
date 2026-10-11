from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash

assert Path.cwd() == ROOT
frozen = load(CONTRACT/'potential-stabilized-v2.json')
context = CONTRACT/'potential-definition-context-v1.lean.txt'
header = CONTRACT/'potential-header-draft-v1.lean.txt'
assert sha(context) == frozen['context_sha256']
assert sha(header) == frozen['header_sha256']
body = '''  have hparts := Finset.sum_range_by_parts w (fun i => a i - a (i + 1)) T
  simp only [smul_eq_mul, Finset.sum_range_sub'] at hparts
  have hlow : (a 0 - C) * (w (T - 1) - w 0) ≤
      ∑ i ∈ range (T - 1), (w (i + 1) - w i) * (a 0 - a (i + 1)) := by
    calc
      (a 0 - C) * (w (T - 1) - w 0) =
          ∑ i ∈ range (T - 1), (w (i + 1) - w i) * (a 0 - C) := by
            rw [← Finset.sum_mul, Finset.sum_range_sub]
            ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hiT : i + 1 < T := by
          have := Finset.mem_range.mp hi
          omega
        exact mul_le_mul_of_nonneg_left
          (sub_le_sub_left (hbound (i + 1) hiT) (a 0))
          (sub_nonneg.mpr (hmono i hiT))
  have hstart : (a 0 - C) * w 0 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hbound 0 hT)) (hw 0 hT)
  have hcomm : (∑ t ∈ range T, (a t - a (t + 1)) * w t) =
      ∑ t ∈ range T, w t * (a t - a (t + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hcomm, hparts]
  nlinarith [hlow, hstart]

end BanditRL.OnlineAdaptivePotential
'''
write(PUBLIC, context.read_bytes() + b'\n' + header.read_bytes() + body.encode('utf8'))
actual_header = lean_declaration_header(PUBLIC, 'weighted_potential_sum')
assert statement_hash(actual_header) == frozen['statement_hash']
snapshot = RUN/'potential-body-attempt-v1.lean.txt'
write(snapshot, PUBLIC.read_bytes())
write(RUN/'potential-body-input-v1.json', dict(
    module=PUBLIC.as_posix(), module_sha256=sha(PUBLIC), snapshot_sha256=sha(snapshot),
    statement_hash=statement_hash(actual_header),
    route='pinned Mathlib sum_range_by_parts; interior upper bound; nonnegative first weight',
    status='actual BODY, pending compiler evidence', parent_algorithm='required-draft'))
code, out = capture('potential-focused-build-v1', 'lake', 'build',
    'BanditRLProof.OnlineAdaptivePotential', required=False)
print(out)
assert statement_hash(lean_declaration_header(PUBLIC, 'weighted_potential_sum')) == frozen['statement_hash']
sys.exit(code)
