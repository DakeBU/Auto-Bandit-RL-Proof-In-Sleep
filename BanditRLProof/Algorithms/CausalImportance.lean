import BanditRLProof.Algorithms.CausalMarginalLaw
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic

/-! Covered finite mixtures and exact importance-weight identities. -/
namespace BanditRLProof.Causal
open scoped Classical
set_option autoImplicit false

noncomputable def mass {Z : Type*} (p : PMF Z) (z : Z) : ℝ := (p z).toReal

theorem mass_nonneg {Z : Type*} (p : PMF Z) (z : Z) : 0 ≤ mass p z :=
  ENNReal.toReal_nonneg

theorem mass_le_one {Z : Type*} (p : PMF Z) (z : Z) : mass p z ≤ 1 := by
  simpa [mass] using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one z)

theorem sum_mass {Z : Type*} [Fintype Z] (p : PMF Z) : ∑ z, mass p z = 1 := by
  simp only [mass]
  rw [← ENNReal.toReal_sum (fun z _ => p.apply_ne_top z)]
  have hs : ∑ z, p z = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [hs, ENNReal.toReal_one]

noncomputable def mixture {A Z : Type*} (eta : PMF A) (p : A → PMF Z) : PMF Z :=
  eta.bind p

theorem mixture_mass {A Z : Type*} [Fintype A] (eta : PMF A) (p : A → PMF Z)
    (z : Z) : mass (mixture eta p) z = ∑ a, mass eta a * mass (p a) z := by
  simp only [mass, mixture, PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (eta.apply_ne_top a)
    ((p a).apply_ne_top z))]
  simp [ENNReal.toReal_mul]

def Covers {A Z : Type*} (p : A → PMF Z) (q : PMF Z) : Prop :=
  ∀ a z, mass (p a) z ≠ 0 → mass q z ≠ 0

noncomputable def ratio {Z : Type*} (p q : PMF Z) (z : Z) : ℝ := mass p z / mass q z

theorem covered_cancel {A Z : Type*} (p : A → PMF Z) (q : PMF Z)
    (hc : Covers p q) (a : A) (z : Z) : mass q z * ratio (p a) q z = mass (p a) z := by
  by_cases hp : mass (p a) z = 0
  · simp [ratio, hp]
  · exact mul_div_cancel₀ _ (hc a z hp)

theorem importance_identity {A Z : Type*} [Fintype Z] (p : A → PMF Z) (q : PMF Z)
    (hc : Covers p q) (a : A) (f : Z → ℝ) :
    ∑ z, mass q z * (ratio (p a) q z * f z) = ∑ z, mass (p a) z * f z := by
  apply Finset.sum_congr rfl
  intro z _
  rw [← mul_assoc, covered_cancel p q hc]

theorem positive_allocation_covers {A Z : Type*} [Fintype A]
    (eta : PMF A) (p : A → PMF Z) (he : ∀ a, 0 < mass eta a) :
    Covers p (mixture eta p) := by
  intro a z hp
  have ha : 0 < mass (p a) z := lt_of_le_of_ne (mass_nonneg _ _) (Ne.symm hp)
  have hterm : 0 < mass eta a * mass (p a) z := mul_pos (he a) ha
  have hle : mass eta a * mass (p a) z ≤ ∑ b, mass eta b * mass (p b) z :=
    Finset.single_le_sum (fun b _ => mul_nonneg (mass_nonneg eta b) (mass_nonneg (p b) z))
      (Finset.mem_univ a)
  rw [mixture_mass]
  exact ne_of_gt (lt_of_lt_of_le hterm hle)

theorem ratio_nonneg {Z : Type*} (p q : PMF Z) (z : Z) : 0 ≤ ratio p q z :=
  div_nonneg (mass_nonneg p z) (mass_nonneg q z)

noncomputable def secondMoment {Z : Type*} [Fintype Z] (p q : PMF Z) : ℝ :=
  ∑ z, mass p z * ratio p q z

theorem ratio_second_moment {A Z : Type*} [Fintype Z] (p : A → PMF Z) (q : PMF Z)
    (hc : Covers p q) (a : A) :
    ∑ z, mass q z * ratio (p a) q z ^ 2 = secondMoment (p a) q := by
  simpa [secondMoment, pow_two] using importance_identity p q hc a (ratio (p a) q)

noncomputable def truncationBias {Z : Type*} [Fintype Z]
    (p q : PMF Z) (r : Z → ℝ) (B : ℝ) : ℝ :=
  ∑ z, if B < ratio p q z then mass p z * r z else 0

noncomputable def truncatedMean {Z : Type*} [Fintype Z]
    (p q : PMF Z) (r : Z → ℝ) (B : ℝ) : ℝ :=
  ∑ z, mass q z * (if ratio p q z ≤ B then ratio p q z * r z else 0)

theorem truncatedMean_add_bias {A Z : Type*} [Fintype Z]
    (p : A → PMF Z) (q : PMF Z) (hc : Covers p q) (a : A)
    (r : Z → ℝ) (B : ℝ) :
    truncatedMean (p a) q r B + truncationBias (p a) q r B =
      ∑ z, mass (p a) z * r z := by
  unfold truncatedMean truncationBias
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : ratio (p a) q z ≤ B
  · simp only [h, not_lt.mpr h, if_true, if_false, add_zero]
    rw [← mul_assoc, covered_cancel p q hc]
  · simp [h, lt_of_not_ge h]

theorem truncationBias_nonneg {Z : Type*} [Fintype Z]
    (p q : PMF Z) (r : Z → ℝ) (hr : ∀ z, 0 ≤ r z) (B : ℝ) :
    0 ≤ truncationBias p q r B := by
  apply Finset.sum_nonneg
  intro z _
  split_ifs
  · exact mul_nonneg (mass_nonneg p z) (hr z)
  · exact le_rfl

theorem truncationBias_le {Z : Type*} [Fintype Z]
    (p q : PMF Z) (r : Z → ℝ) (hr : ∀ z, r z ≤ 1)
    (B : ℝ) (hB : 0 < B) : truncationBias p q r B ≤ secondMoment p q / B := by
  apply (le_div_iff₀ hB).mpr
  unfold truncationBias secondMoment
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z _
  by_cases h : B < ratio p q z
  · simp only [h, if_true]
    calc
      mass p z * r z * B ≤ mass p z * 1 * B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hr z) (mass_nonneg p z)) hB.le
      _ ≤ mass p z * ratio p q z := by
        simpa using mul_le_mul_of_nonneg_left h.le (mass_nonneg p z)
  · simp only [h, if_false, zero_mul]
    exact mul_nonneg (mass_nonneg p z) (ratio_nonneg p q z)

noncomputable def pairedLaw {Z V : Type*} (p : PMF Z) (k : Z → PMF V) : PMF (Z × V) :=
  p.bind (fun z => (k z).map (fun y => (z,y)))

theorem mixture_pairedLaw {A Z V : Type*} (eta : PMF A) (p : A → PMF Z)
    (k : Z → PMF V) : mixture eta (fun a => pairedLaw (p a) k) =
      pairedLaw (mixture eta p) k := by
  simp [mixture, pairedLaw, PMF.bind_bind]

theorem pairedLaw_mass {Z V : Type*} (p : PMF Z) (k : Z → PMF V) (z : Z) (y : V) :
    mass (pairedLaw p k) (z,y) = mass p z * mass (k z) y := by
  simp only [mass, pairedLaw, paired_mass, ENNReal.toReal_mul]

noncomputable def weightedBit {Z : Type*} (p q : PMF Z) (B : ℝ) (zy : Z × Bool) : ℝ :=
  if zy.2 && decide (ratio p q zy.1 ≤ B) then ratio p q zy.1 else 0

theorem weightedBit_mean {Z : Type*} [Fintype Z] (p q : PMF Z)
    (k : Z → PMF Bool) (B : ℝ) :
    (∑ z, ∑ y : Bool, mass (pairedLaw q k) (z,y) * weightedBit p q B (z,y)) =
      truncatedMean p q (fun z => mass (k z) true) B := by
  apply Finset.sum_congr rfl
  intro z _
  simp only [Fintype.sum_bool, weightedBit, Bool.false_and, Bool.true_and,
    Bool.false_eq_true, if_false, mul_zero, decide_eq_true_eq, pairedLaw_mass]
  by_cases h : ratio p q z ≤ B <;> simp [h, mul_comm, mul_assoc]

theorem weightedBit_bounds {Z : Type*} (p q : PMF Z) (B : ℝ) (hB : 0 ≤ B)
    (zy : Z × Bool) : 0 ≤ weightedBit p q B zy ∧ weightedBit p q B zy ≤ B := by
  unfold weightedBit
  split_ifs with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨ratio_nonneg p q _, h.2⟩
  · exact ⟨le_rfl, hB⟩

theorem weightedBit_second_le {A Z : Type*} [Fintype Z]
    (p : A → PMF Z) (q : PMF Z) (hc : Covers p q) (a : A)
    (k : Z → PMF Bool) (B : ℝ) :
    (∑ z, ∑ y : Bool, mass (pairedLaw q k) (z,y) * weightedBit (p a) q B (z,y)^2) ≤
      secondMoment (p a) q := by
  rw [← ratio_second_moment p q hc a]
  apply Finset.sum_le_sum
  intro z _
  simp only [Fintype.sum_bool, weightedBit, Bool.false_and, Bool.true_and,
    Bool.false_eq_true, if_false, zero_pow (by decide : 2 ≠ 0), mul_zero,
    add_zero, decide_eq_true_eq, pairedLaw_mass]
  by_cases h : ratio (p a) q z ≤ B
  · simp only [h, if_true]
    have hm : mass q z * mass (k z) true ≤ mass q z := by
      simpa using mul_le_mul_of_nonneg_left (mass_le_one (k z) true) (mass_nonneg q z)
    exact mul_le_mul_of_nonneg_right hm (sq_nonneg _)
  · simp only [h, if_false, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact mul_nonneg (mass_nonneg q z) (sq_nonneg _)

theorem GraphModel.mixture_parent_joint {A V : Type*} [Inhabited V] {n : ℕ}
    (g : GraphModel V n) (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none) :
    mixture eta (fun a => (joint (g.doModel (actions a)).table).map
      (fun x => (g.parentConfig i (history x i),x i))) =
    pairedLaw (mixture eta (fun a => g.parentLaw (actions a) i)) (g.parentTable i) := by
  simp_rw [g.intervention_parent_joint _ i (hi _)]
  exact mixture_pairedLaw eta _ _

end BanditRLProof.Causal
