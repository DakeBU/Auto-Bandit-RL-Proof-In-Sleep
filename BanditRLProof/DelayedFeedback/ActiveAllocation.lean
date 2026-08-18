import Mathlib
import BanditRLProof.DelayedFeedback.CausalView

namespace BanditRLProof

namespace DelayedFeedback

open scoped BigOperators

/-- Arms outside the current active set in Algorithm 5. -/
def inactiveArms {K : Nat} (active : Finset (Fin K)) : Finset (Fin K) :=
  Finset.univ \ active

/-- Algorithm 5 line 15 assigns the residual mass equally to active arms. -/
noncomputable def activeEqualShare {K : Nat}
    (active : Finset (Fin K)) (inactiveProbability : Fin K → ℝ) : ℝ :=
  (1 - ∑ i ∈ inactiveArms active, inactiveProbability i) /
    (active.card : ℝ)

/-- Full probability vector obtained from externally maintained probabilities
on eliminated arms and equal residual mass on active arms. -/
noncomputable def delayedSAPOProbability {K : Nat}
    (active : Finset (Fin K)) (inactiveProbability : Fin K → ℝ)
    (i : Fin K) : ℝ :=
  if i ∈ active then activeEqualShare active inactiveProbability
  else inactiveProbability i

@[simp]
theorem delayedSAPOProbability_of_active {K : Nat}
    (active : Finset (Fin K)) (inactiveProbability : Fin K → ℝ)
    {i : Fin K} (hi : i ∈ active) :
    delayedSAPOProbability active inactiveProbability i =
      activeEqualShare active inactiveProbability := by
  simp [delayedSAPOProbability, hi]

@[simp]
theorem delayedSAPOProbability_of_inactive {K : Nat}
    (active : Finset (Fin K)) (inactiveProbability : Fin K → ℝ)
    {i : Fin K} (hi : i ∉ active) :
    delayedSAPOProbability active inactiveProbability i =
      inactiveProbability i := by
  simp [delayedSAPOProbability, hi]

/-- The residual active-arm share is nonnegative when eliminated-arm mass does
not exceed one. -/
theorem activeEqualShare_nonneg {K : Nat}
    (active : Finset (Fin K)) (inactiveProbability : Fin K → ℝ)
    (hmass : (∑ i ∈ inactiveArms active, inactiveProbability i) ≤ 1) :
    0 ≤ activeEqualShare active inactiveProbability := by
  exact div_nonneg (sub_nonneg.mpr hmass) (Nat.cast_nonneg active.card)

/-- Every coordinate of the line-15 allocation is nonnegative under the
source-side residual-mass and inactive-coordinate hypotheses. -/
theorem delayedSAPOProbability_nonneg {K : Nat}
    (active : Finset (Fin K)) (inactiveProbability : Fin K → ℝ)
    (hinactive : ∀ i ∈ inactiveArms active, 0 ≤ inactiveProbability i)
    (hmass : (∑ i ∈ inactiveArms active, inactiveProbability i) ≤ 1)
    (i : Fin K) :
    0 ≤ delayedSAPOProbability active inactiveProbability i := by
  by_cases hi : i ∈ active
  · rw [delayedSAPOProbability_of_active active inactiveProbability hi]
    exact activeEqualShare_nonneg active inactiveProbability hmass
  · rw [delayedSAPOProbability_of_inactive active inactiveProbability hi]
    exact hinactive i (by simp [inactiveArms, hi])

/-- With at least one active arm, the equal-residual allocation has total mass
exactly one. -/
theorem sum_delayedSAPOProbability_eq_one {K : Nat}
    (active : Finset (Fin K)) (inactiveProbability : Fin K → ℝ)
    (hactive : active.Nonempty) :
    ∑ i, delayedSAPOProbability active inactiveProbability i = 1 := by
  classical
  have hcardNat : active.card ≠ 0 := Finset.card_ne_zero.mpr hactive
  have hcardReal : (active.card : ℝ) ≠ 0 := by
    exact_mod_cast hcardNat
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun i : Fin K => i ∈ active)
    (f := delayedSAPOProbability active inactiveProbability)]
  have hactiveFilter :
      Finset.univ.filter (fun i : Fin K => i ∈ active) = active := by
    ext i
    simp
  have hinactiveFilter :
      Finset.univ.filter (fun i : Fin K => ¬ i ∈ active) =
        inactiveArms active := by
    ext i
    simp [inactiveArms]
  rw [hactiveFilter, hinactiveFilter]
  have hactiveSum :
      ∑ i ∈ active, delayedSAPOProbability active inactiveProbability i =
        (active.card : ℝ) * activeEqualShare active inactiveProbability := by
    calc
      ∑ i ∈ active, delayedSAPOProbability active inactiveProbability i =
          ∑ _i ∈ active, activeEqualShare active inactiveProbability := by
            apply Finset.sum_congr rfl
            intro i hi
            exact delayedSAPOProbability_of_active active inactiveProbability hi
      _ = (active.card : ℝ) * activeEqualShare active inactiveProbability := by
        simp
  have hinactiveSum :
      ∑ i ∈ inactiveArms active,
          delayedSAPOProbability active inactiveProbability i =
        ∑ i ∈ inactiveArms active, inactiveProbability i := by
    apply Finset.sum_congr rfl
    intro i hi
    apply delayedSAPOProbability_of_inactive
    simpa [inactiveArms] using hi
  rw [hactiveSum, hinactiveSum]
  unfold activeEqualShare
  field_simp [hcardReal]
  ring

end DelayedFeedback

end BanditRLProof
