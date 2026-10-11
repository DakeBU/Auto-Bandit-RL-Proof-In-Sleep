import BanditRLProof.OnlineAdaptivePotential
open Finset

example (a w : ℕ → ℝ) (C : ℝ) (T : ℕ) (hT : 0 < T)
    (hw : ∀ t < T, 0 ≤ w t)
    (hmono : ∀ t, t + 1 < T → w t ≤ w (t + 1))
    (hbound : ∀ t < T, a t ≤ C) :
    (∑ t ∈ range T, (a t - a (t + 1)) * w t) ≤
      C * w (T - 1) - a T * w (T - 1) :=
  BanditRL.OnlineAdaptivePotential.weighted_potential_sum a w C T hT hw hmono hbound

#check BanditRL.OnlineAdaptivePotential.weighted_potential_sum
#print BanditRL.OnlineAdaptivePotential.weighted_potential_sum
#print axioms BanditRL.OnlineAdaptivePotential.weighted_potential_sum
