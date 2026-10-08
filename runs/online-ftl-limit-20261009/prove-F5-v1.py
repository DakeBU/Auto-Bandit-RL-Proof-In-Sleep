from append_leaf_v1 import *
append_leaf('F5','''  have hfixed : ∀ u : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - y t)^2) (meanPredict y) u T / (T : ℝ))
      atTop (nhds (-(u - m)^2)) := by
    intro u
    apply (meanPredict_fixedRegret_limit_iff y hy u (-(u - m)^2)).mpr
    simpa only [neg_neg] using (tendsto_const_nhds.sub hm).pow 2
  refine ⟨hfixed, ?_⟩
  intro u hu
  exact ⟨-(u - m)^2, neg_nonpos.mpr (sq_nonneg _), hfixed u⟩
''',requires=['F4'])
