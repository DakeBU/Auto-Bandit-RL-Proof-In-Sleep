import BanditRLProof.OnlineGammaEstimates

open Filter Set MeasureTheory
open scoped Interval Topology

namespace BanditRL.OnlineGamma
noncomputable section

private theorem hasDerivAt_neg_shifted_reciprocal (x t : ℝ) (h : x + t ≠ 0) :
    HasDerivAt (fun s : ℝ => -(x+s)⁻¹) (1/(x+t)^2) t := by
  simpa [Pi.neg_apply, Pi.inv_apply, neg_div] using
    ((((hasDerivAt_id t).const_add x).inv h).neg)

theorem midpointInvSq_unitCell_integral :
  ∀ (x : ℝ) (k : ℕ), 0 < x →
    (1 / (x + (k : ℝ) + 1/2)^2 ≤
      ∫ t in (k : ℝ)..((k : ℝ) + 1), 1 / (x + t)^2) ∧
    (∫ t in (k : ℝ)..((k : ℝ) + 1), 1 / (x + t)^2) =
      1 / (x + (k : ℝ)) - 1 / (x + (k : ℝ) + 1) := by
  intro x k hx
  have hab : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hpos (t : ℝ) (ht : (k : ℝ) ≤ t) : 0 < x + t :=
    add_pos_of_pos_of_nonneg hx ((Nat.cast_nonneg k).trans ht)
  have hcont : ContinuousOn (fun t : ℝ => 1 / (x+t)^2)
      (Icc (k : ℝ) ((k : ℝ)+1)) := by
    apply continuousOn_const.div ((continuous_const.add continuous_id).pow 2).continuousOn
    intro t ht
    exact pow_ne_zero _ (hpos t ht.1).ne'
  have hcell := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (f := fun t : ℝ => -(x+t)⁻¹)
    (fun t ht => (hasDerivAt_neg_shifted_reciprocal x t (hpos t ht.1).ne').continuousAt.continuousWithinAt)
    (fun t ht => hasDerivAt_neg_shifted_reciprocal x t (hpos t ht.1.le).ne')
    (hcont.intervalIntegrable_of_Icc hab)
  have heq : (∫ t in (k : ℝ)..((k : ℝ)+1), 1/(x+t)^2) =
      1/(x+(k : ℝ)) - 1/(x+(k : ℝ)+1) := by
    simpa [one_div, ← add_assoc, sub_eq_add_neg, add_comm] using hcell
  exact ⟨(midpointInvSq_le_reciprocalDifference x hx k).trans_eq heq.symm, heq⟩

theorem midpointInvSq_ray_integral :
  ∀ (x : ℝ), 0 < x →
    IntegrableOn (fun t : ℝ => 1 / (x + t)^2) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), 1 / (x + t)^2) = 1 / x ∧
    (∑' k : ℕ, 1 / (x + (k : ℝ) + 1/2)^2) ≤
      ∫ t in Ioi (0 : ℝ), 1 / (x + t)^2 := by
  intro x hx
  have hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s : ℝ => -(x+s)⁻¹) (1/(x+t)^2) t :=
    fun t ht => hasDerivAt_neg_shifted_reciprocal x t (add_pos_of_pos_of_nonneg hx ht).ne'
  have hshift : Tendsto (fun t : ℝ => x+t) atTop atTop :=
    tendsto_const_nhds.add_atTop tendsto_id
  have hlim : Tendsto (fun t : ℝ => -(x+t)⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_inv_atTop_zero.comp hshift).neg
  have hi := MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hd
    (fun t _ => by positivity) hlim
  have heq : (∫ t in Ioi (0 : ℝ), 1/(x+t)^2) = 1/x := by
    simpa [one_div] using MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hd hi hlim
  exact ⟨hi, heq, (summable_midpointInvSq_and_tsum_le x hx).2.trans_eq heq.symm⟩

end
end BanditRL.OnlineGamma