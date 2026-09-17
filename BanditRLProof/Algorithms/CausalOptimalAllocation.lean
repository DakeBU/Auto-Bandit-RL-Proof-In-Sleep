import BanditRLProof.Algorithms.CausalAllocation
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact

/-! Attainment of the covered finite causal allocation objective. -/
namespace BanditRLProof.Causal
open scoped Classical
set_option autoImplicit false

variable {A Z : Type*} [Fintype A] [Nonempty A] [Fintype Z]

noncomputable def allocationOfWeights (w : A → ℝ) (hw : w ∈ stdSimplex ℝ A) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (w a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hw.1 a), hw.2]
    simp)

omit [Nonempty A] in
theorem allocationOfWeights_mass (w : A → ℝ) (hw : w ∈ stdSimplex ℝ A) (a : A) :
    mass (allocationOfWeights w hw) a = w a := by
  simp [mass, allocationOfWeights, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hw.1 a)]

omit [Nonempty A] in
theorem mass_mem_simplex (eta : PMF A) : mass eta ∈ stdSimplex ℝ A :=
  ⟨mass_nonneg eta, sum_mass eta⟩

noncomputable def mixtureWeight (p : A → PMF Z) (w : A → ℝ) (z : Z) : ℝ :=
  ∑ a, w a * mass (p a) z

noncomputable def coordinateCost (p : A → PMF Z) (w : A → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a => ∑ z, mass (p a) z ^ 2 / mixtureWeight p w z)

theorem coordinateCost_mass (p : A → PMF Z) (eta : PMF A) :
    coordinateCost p (mass eta) = designCost p eta := by
  unfold coordinateCost designCost
  congr 1
  funext a
  apply Finset.sum_congr rfl
  intro z _
  simp only [ratio, mixture_mass, mixtureWeight]
  ring

def safeAllocations (p : A → PMF Z) : Set (A → ℝ) :=
  stdSimplex ℝ A ∩ {w | ∀ a z, mass (p a) z ^ 2 / (Fintype.card A : ℝ) ≤ mixtureWeight p w z}

omit [Nonempty A] [Fintype Z] in
theorem continuous_mixtureWeight (p : A → PMF Z) (z : Z) :
    Continuous (fun w => mixtureWeight p w z) := by
  unfold mixtureWeight
  fun_prop

omit [Nonempty A] [Fintype Z] in
theorem safeAllocations_compact (p : A → PMF Z) : IsCompact (safeAllocations p) := by
  apply (isCompact_stdSimplex ℝ A).inter_right
  have heq : {w | ∀ a z, mass (p a) z ^ 2 / (Fintype.card A : ℝ) ≤ mixtureWeight p w z} =
      ⋂ a, ⋂ z, {w | mass (p a) z ^ 2 / (Fintype.card A : ℝ) ≤ mixtureWeight p w z} := by
    ext w
    simp
  rw [heq]
  exact isClosed_iInter (fun a => isClosed_iInter (fun z =>
    isClosed_le continuous_const (continuous_mixtureWeight p z)))

theorem sublevel_mem_safe (p : A → PMF Z) (eta : PMF A)
    (hc : Covers p (mixture eta p)) (hcost : designCost p eta ≤ Fintype.card A) :
    mass eta ∈ safeAllocations p := by
  refine ⟨mass_mem_simplex eta, fun a z => ?_⟩
  simpa [mixtureWeight, mixture_mass] using design_sublevel_mass_lower p eta hc
    (Fintype.card A) (by exact_mod_cast Fintype.card_pos) hcost a z

theorem uniform_mem_safe (p : A → PMF Z) : mass (PMF.uniformOfFintype A) ∈ safeAllocations p :=
  sublevel_mem_safe p _ (uniform_covers p) (uniform_designCost_le_card p)

omit [Fintype Z] in
theorem safe_denominator_pos (p : A → PMF Z) (w : A → ℝ) (hw : w ∈ safeAllocations p)
    (a : A) (z : Z) (hp : mass (p a) z ≠ 0) : 0 < mixtureWeight p w z := by
  have hK : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  exact lt_of_lt_of_le (div_pos (sq_pos_of_ne_zero hp) hK) (hw.2 a z)

theorem coordinateCost_continuousOn (p : A → PMF Z) :
    ContinuousOn (coordinateCost p) (safeAllocations p) := by
  apply ContinuousOn.finset_sup'_apply
  intro a _
  apply continuousOn_finset_sum
  intro z _
  by_cases hp : mass (p a) z = 0
  · simpa [hp] using (continuousOn_const : ContinuousOn (fun _ : A → ℝ => (0 : ℝ)) _)
  · exact continuousOn_const.div (continuous_mixtureWeight p z).continuousOn
      (fun w hw => ne_of_gt (safe_denominator_pos p w hw a z hp))

omit [Fintype Z] in
theorem safe_allocation_covers (p : A → PMF Z) (w : A → ℝ) (hw : w ∈ safeAllocations p) :
    Covers p (mixture (allocationOfWeights w hw.1) p) := by
  intro a z hp
  have hpos := safe_denominator_pos p w hw a z hp
  simpa [mixture_mass, allocationOfWeights_mass, mixtureWeight] using ne_of_gt hpos

theorem exists_optimal_allocation (p : A → PMF Z) :
    ∃ eta : PMF A, Covers p (mixture eta p) ∧ designCost p eta ≤ Fintype.card A ∧
      ∀ eta' : PMF A, Covers p (mixture eta' p) → designCost p eta ≤ designCost p eta' := by
  obtain ⟨w, hw, hmin⟩ := (safeAllocations_compact p).exists_isMinOn
    ⟨_, uniform_mem_safe p⟩ (coordinateCost_continuousOn p)
  let eta := allocationOfWeights w hw.1
  have hmass : mass eta = w := funext (allocationOfWeights_mass w hw.1)
  have heq : coordinateCost p w = designCost p eta := by
    rw [← hmass, coordinateCost_mass]
  have hbound : designCost p eta ≤ Fintype.card A := by
    have h : coordinateCost p w ≤ coordinateCost p (mass (PMF.uniformOfFintype A)) :=
      hmin (uniform_mem_safe p)
    rw [heq, coordinateCost_mass] at h
    exact h.trans (uniform_designCost_le_card p)
  refine ⟨eta, safe_allocation_covers p w hw, hbound, ?_⟩
  intro eta' hc
  by_cases hcost : designCost p eta' ≤ Fintype.card A
  · have h : coordinateCost p w ≤ coordinateCost p (mass eta') :=
      hmin (sublevel_mem_safe p eta' hc hcost)
    simpa only [heq, coordinateCost_mass] using h
  · exact hbound.trans (le_of_not_ge hcost)

noncomputable def optimalAllocation (p : A → PMF Z) : PMF A :=
  (exists_optimal_allocation p).choose

theorem optimalAllocation_covers (p : A → PMF Z) : Covers p (mixture (optimalAllocation p) p) :=
  (exists_optimal_allocation p).choose_spec.1

theorem optimalAllocation_cost_le_card (p : A → PMF Z) :
    designCost p (optimalAllocation p) ≤ Fintype.card A :=
  (exists_optimal_allocation p).choose_spec.2.1

theorem optimalAllocation_minimizes (p : A → PMF Z) (eta : PMF A)
    (hc : Covers p (mixture eta p)) : designCost p (optimalAllocation p) ≤ designCost p eta :=
  (exists_optimal_allocation p).choose_spec.2.2 eta hc

theorem secondMoment_self (q : PMF Z) : secondMoment q q = 1 := by
  have h (z : Z) : mass q z * ratio q q z = mass q z :=
    covered_cancel (fun _ : Unit => q) q (fun _ _ hp => hp) () z
  simp only [secondMoment, h, sum_mass]

theorem constant_designCost (q : PMF Z) (eta : PMF A) :
    designCost (fun _ : A => q) eta = 1 := by
  simp [designCost, mixture, secondMoment_self]

end BanditRLProof.Causal
