import BanditRLProof.Algorithms.CausalParallelDesign

/-! Actual independent-root intervention laws and their covered allocation cost. -/
namespace BanditRLProof.Causal
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mixture_mass_ge_component {A Z : Type*} [Fintype A]
    (eta : PMF A) (p : A → PMF Z) (a : A) (z : Z) :
    mass eta a * mass (p a) z ≤ mass (mixture eta p) z := by
  rw [mixture_mass]
  exact Finset.single_le_sum (fun b _ => mul_nonneg (mass_nonneg eta b)
    (mass_nonneg (p b) z)) (Finset.mem_univ a)

namespace ParallelParameters
variable {N : ℕ} (p : ParallelParameters N)

noncomputable def rootTable (i : Fin N) : PMF Bool :=
  PMF.bernoulli ⟨p.q i,p.nonneg i⟩ (p.le_one i)

theorem rootTable_mass (i : Fin N) (b : Bool) : mass (p.rootTable i) b = p.valueProbability (i,b) := by
  have hq : (⟨p.q i,p.nonneg i⟩:NNReal) ≤ 1 := p.le_one i
  have he : ENNReal.ofNNReal ⟨p.q i,p.nonneg i⟩ ≤ 1 := ENNReal.coe_le_one_iff.mpr hq
  cases b <;> simp [rootTable, mass, PMF.bernoulli_apply, valueProbability,
    ENNReal.toReal_sub_of_le he ENNReal.one_ne_top]

def rootAction (a : Option (Fin N × Bool)) (i : Fin N) : Option Bool :=
  a.bind fun b => if i = b.1 then some b.2 else none

noncomputable def rootLaw (a : Option (Fin N × Bool)) : PMF (Fin N → Bool) :=
  joint (intervene (fun i _ => p.rootTable i) (rootAction a))

theorem rootLaw_mass (a : Option (Fin N × Bool)) (x : Fin N → Bool) :
    mass (p.rootLaw a) x = ∏ i, match a with
      | none => p.valueProbability (i,x i)
      | some b => if i = b.1 then (if x i = b.2 then 1 else 0)
          else p.valueProbability (i,x i) := by
  unfold mass rootLaw
  rw [joint_factorization, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases a with
  | none => simpa [intervene,rootAction] using p.rootTable_mass i (x i)
  | some b =>
    by_cases hi : i = b.1
    · subst i
      by_cases hx : x b.1 = b.2 <;> simp [intervene,rootAction,hx,PMF.pure_apply]
    · simpa [intervene,rootAction,hi] using p.rootTable_mass i (x i)

theorem rootLaw_atom_mass (i : Fin N) (b : Bool) (x : Fin N → Bool) :
    mass (p.rootLaw (some (i,b))) x =
      (if x i = b then 1 else 0) * ∏ j ∈ Finset.univ.erase i, p.valueProbability (j,x j) := by
  rw [rootLaw_mass, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

theorem atomic_observational_domination (a : Fin N × Bool) (x : Fin N → Bool) :
    p.valueProbability a * mass (p.rootLaw (some a)) x ≤ mass (p.rootLaw none) x := by
  rcases a with ⟨i,b⟩
  rw [rootLaw_atom_mass]
  by_cases hx : x i = b
  · rw [if_pos hx, one_mul, rootLaw_mass,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [hx, le_refl]
  · rw [if_neg hx,zero_mul,mul_zero]
    exact mass_nonneg _ _

theorem allocated_mass_domination (a : Option (Fin N × Bool)) (x : Fin N → Bool) :
    mass (p.rootLaw a) x ≤ (2*p.rarity)*mass (mixture p.allocation p.rootLaw) x := by
  have hq := mass_nonneg (mixture p.allocation p.rootLaw) x
  have hm := p.rarity_pos
  have hm2 : (2:ℝ) ≤ p.rarity := by exact_mod_cast p.rarity_spec.1
  have hempty : (1/2)*mass (p.rootLaw none) x ≤ mass (mixture p.allocation p.rootLaw) x :=
    (mul_le_mul_of_nonneg_right p.allocation_empty_ge_half (mass_nonneg _ _)).trans
      (mixture_mass_ge_component p.allocation p.rootLaw none x)
  cases a with
  | none => nlinarith
  | some a =>
    by_cases ha : a ∈ p.rareActions
    · have h := mixture_mass_ge_component p.allocation p.rootLaw (some a) x
      rw [p.allocation_mass] at h
      simp only [allocationWeight,ha,if_true,rareWeight] at h
      have hc : (2*(p.rarity:ℝ)) * (1/(2*p.rarity)) = 1 := by field_simp
      have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*(p.rarity:ℝ) by positivity)
      rw [← mul_assoc,hc,one_mul] at hh
      exact hh
    · have hr : 1/(p.rarity:ℝ) ≤ p.valueProbability a := by
        simpa [rareActions] using ha
      have hdom := p.atomic_observational_domination a x
      have hbase := (mul_le_mul_of_nonneg_right hr (mass_nonneg (p.rootLaw (some a)) x)).trans hdom
      have hscaled := mul_le_mul_of_nonneg_left hbase hm.le
      have hc : (p.rarity:ℝ) * (1/p.rarity) = 1 := by field_simp
      rw [← mul_assoc,hc,one_mul] at hscaled
      have hmix := mul_le_mul_of_nonneg_left hempty hm.le
      nlinarith

theorem allocation_covers : Covers p.rootLaw (mixture p.allocation p.rootLaw) :=
  covers_of_mass_domination _ _ _ p.allocated_mass_domination

theorem allocation_cost_le : designCost p.rootLaw p.allocation ≤ 2*p.rarity := by
  apply Finset.sup'_le
  intro a _
  exact secondMoment_le_of_mass_domination _ _ _ (by positivity)
    (p.allocated_mass_domination a)

theorem optimal_cost_le : designCost p.rootLaw (optimalAllocation p.rootLaw) ≤ 2*p.rarity :=
  (optimalAllocation_minimizes p.rootLaw p.allocation p.allocation_covers).trans p.allocation_cost_le

end ParallelParameters
end BanditRLProof.Causal
