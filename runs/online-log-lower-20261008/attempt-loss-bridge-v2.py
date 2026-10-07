from common_v1 import *
write(RUN/'loss-bridge-repair-v2.json',dict(prior_exit=load(RUN/'loss-bridge-attempt-v1-exit.json')['exit_code'],
    prior_log_sha256=sha(RUN/'loss-bridge-attempt-v1.log'),
    cause='Mean substitution unfolded the explicit comparator sum but not the auxiliary pathBestLoss; ordered-add convenience lemma used opposite term order.',
    correction='Bind the substituted comparator sum to the same pathBestLoss by an exact equality; use add_le_add le_rfl.',
    source_or_frozen_target_changed=False))
original=(RUN/'leaves/loss-bridge-v1.lean').read_text(encoding='utf-8')
old='  change (h.count true : ℝ) = pathBestLoss h + (h.count true : ℝ)^2 / (h.length : ℝ) at hd'
new='''  have hb : pathBestLoss h = ∑ t ∈ range h.length,
      ((h.count true : ℝ) / h.length - binaryValues h t)^2 := by
    simp only [pathBestLoss, hm]
  rw [← hb] at hd'''
assert original.count(old)==1
original=original.replace(old,new)
original=original.replace('  exact add_le_add_left (pathExpectation_mono T _ _\n    (fun h _ => conditional_square_lower h (A h))) _',
    '  exact add_le_add le_rfl (pathExpectation_mono T _ _\n    (fun h _ => conditional_square_lower h (A h)))')
write(RUN/'leaves/loss-bridge-v2.lean',original)
gate('loss-bridge-attempt-v2','lake','env','lean',RUN/'leaves/loss-bridge-v2.lean')
