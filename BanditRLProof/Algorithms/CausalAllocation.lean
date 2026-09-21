import BanditRLProof.Algorithms.CausalImportance
import Mathlib.Probability.Distributions.Uniform

/-! Allocation bounds for the actual finite mixture design objective. -/
namespace BanditRLProof.Causal
open scoped Classical NNReal
set_option autoImplicit false

theorem secondMoment_ge_one {A Z : Type*} [Fintype Z]
    (p : A → PMF Z) (q : PMF Z) (hc : Covers p q) (a : A) :
    1 ≤ secondMoment (p a) q := by
  have hmean : ∑ z, mass q z * ratio (p a) q z = 1 := by
    simpa [sum_mass] using importance_identity p q hc a (fun _ => 1)
  have hsq := ratio_second_moment p q hc a
  have hpos : 0 ≤ ∑ z, mass q z * (ratio (p a) q z - 1)^2 :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (mass_nonneg q z) (sq_nonneg _))
  have heq : (∑ z, mass q z * (ratio (p a) q z - 1)^2) =
      (∑ z, mass q z * ratio (p a) q z^2) -
        2 * (∑ z, mass q z * ratio (p a) q z) + ∑ z, mass q z := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [heq, hsq, hmean, sum_mass] at hpos
  linarith

theorem uniform_mass {A : Type*} [Fintype A] [Nonempty A] (a : A) :
    mass (PMF.uniformOfFintype A) a = (Fintype.card A : ℝ)⁻¹ := by
  simp [mass, PMF.uniformOfFintype_apply, ENNReal.toReal_inv]

theorem uniform_covers {A Z : Type*} [Fintype A] [Nonempty A]
    (p : A → PMF Z) : Covers p (mixture (PMF.uniformOfFintype A) p) := by
  apply positive_allocation_covers
  intro a
  rw [uniform_mass]
  exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

theorem uniform_ratio_le_card {A Z : Type*} [Fintype A] [Nonempty A]
    (p : A → PMF Z) (a : A) (z : Z) :
    ratio (p a) (mixture (PMF.uniformOfFintype A) p) z ≤ Fintype.card A := by
  have hK : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  by_cases hp : mass (p a) z = 0
  · simp [ratio, hp, hK.le]
  have hq : 0 < mass (mixture (PMF.uniformOfFintype A) p) z :=
    lt_of_le_of_ne (mass_nonneg _ _) (Ne.symm (uniform_covers p a z hp))
  apply (div_le_iff₀ hq).mpr
  have hle : mass (PMF.uniformOfFintype A) a * mass (p a) z ≤
      mass (mixture (PMF.uniformOfFintype A) p) z := by
    rw [mixture_mass]
    exact Finset.single_le_sum (fun b _ => mul_nonneg
      (mass_nonneg (PMF.uniformOfFintype A) b) (mass_nonneg (p b) z)) (Finset.mem_univ a)
  rw [uniform_mass, ← div_eq_inv_mul] at hle
  exact (div_le_iff₀ hK).mp hle |>.trans_eq (mul_comm _ _)

theorem uniform_secondMoment_le_card {A Z : Type*} [Fintype A] [Nonempty A]
    [Fintype Z] (p : A → PMF Z) (a : A) :
    secondMoment (p a) (mixture (PMF.uniformOfFintype A) p) ≤ Fintype.card A := by
  calc
    _ ≤ ∑ z, mass (p a) z * (Fintype.card A : ℝ) :=
      Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left
        (uniform_ratio_le_card p a z) (mass_nonneg (p a) z))
    _ = _ := by rw [← Finset.sum_mul, sum_mass, one_mul]

noncomputable def designCost {A Z : Type*} [Fintype A] [Nonempty A] [Fintype Z]
    (p : A → PMF Z) (eta : PMF A) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => secondMoment (p a) (mixture eta p))

theorem secondMoment_le_designCost {A Z : Type*} [Fintype A] [Nonempty A] [Fintype Z]
    (p : A → PMF Z) (eta : PMF A) (a : A) :
    secondMoment (p a) (mixture eta p) ≤ designCost p eta :=
  Finset.le_sup' (fun b => secondMoment (p b) (mixture eta p)) (Finset.mem_univ a)

theorem designCost_ge_one {A Z : Type*} [Fintype A] [Nonempty A] [Fintype Z]
    (p : A → PMF Z) (eta : PMF A) (hc : Covers p (mixture eta p)) :
    1 ≤ designCost p eta :=
  (secondMoment_ge_one p _ hc (Classical.arbitrary A)).trans
    (secondMoment_le_designCost p eta _)

theorem uniform_designCost_le_card {A Z : Type*} [Fintype A] [Nonempty A] [Fintype Z]
    (p : A → PMF Z) : designCost p (PMF.uniformOfFintype A) ≤ Fintype.card A := by
  apply Finset.sup'_le
  intro a _
  exact uniform_secondMoment_le_card p a

noncomputable def convexLaw {Z : Type*} (t : ℝ≥0) (ht : t ≤ 1) (p q : PMF Z) : PMF Z :=
  mixture (PMF.bernoulli t ht) (fun b => if b then p else q)

theorem convexLaw_mass {Z : Type*} (t : ℝ≥0) (ht : t ≤ 1) (p q : PMF Z) (z : Z) :
    mass (convexLaw t ht p q) z = (t : ℝ) * mass p z + (1-(t : ℝ)) * mass q z := by
  rw [convexLaw, mixture_mass]
  simp [mass, PMF.bernoulli_apply,
    NNReal.coe_sub ht]

theorem inverse_convex (x y t : ℝ) (hx : 0 < x) (hy : 0 < y)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (t*x+(1-t)*y)⁻¹ ≤ t*x⁻¹+(1-t)*y⁻¹ := by
  have hd : 0 < t*x+(1-t)*y := by
    by_cases h : t = 0
    · simp [h, hy]
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ht (Ne.symm h)) hx)
        (mul_nonneg (sub_nonneg.mpr ht1) hy.le)
  apply (mul_le_mul_iff_right₀ (mul_pos (mul_pos hx hy) hd)).mp
  have hs : 0 ≤ t*(1-t)*(x-y)^2 :=
    mul_nonneg (mul_nonneg ht (sub_nonneg.mpr ht1)) (sq_nonneg _)
  field_simp [hx.ne', hy.ne', hd.ne']
  have hd' : x*t+y*(1-t) ≠ 0 := by nlinarith
  simp only [mul_div_cancel_right₀ _ hd']
  nlinarith

theorem convexLaw_covers {A Z : Type*} (p : A → PMF Z) (q₀ q₁ : PMF Z)
    (hc₀ : Covers p q₀) (hc₁ : Covers p q₁) (t : ℝ≥0) (ht : t ≤ 1) :
    Covers p (convexLaw t ht q₀ q₁) := by
  intro a z hp
  have hx : 0 < mass q₀ z := lt_of_le_of_ne (mass_nonneg _ _) (Ne.symm (hc₀ a z hp))
  have hy : 0 < mass q₁ z := lt_of_le_of_ne (mass_nonneg _ _) (Ne.symm (hc₁ a z hp))
  rw [convexLaw_mass]
  have ht1 : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  by_cases h : (t : ℝ) = 0
  · simpa [h] using ne_of_gt hy
  · exact ne_of_gt (add_pos_of_pos_of_nonneg
      (mul_pos (lt_of_le_of_ne t.coe_nonneg (Ne.symm h)) hx)
      (mul_nonneg (sub_nonneg.mpr ht1) hy.le))

theorem secondMoment_convex {A Z : Type*} [Fintype Z]
    (p : A → PMF Z) (q₀ q₁ : PMF Z) (hc₀ : Covers p q₀) (hc₁ : Covers p q₁)
    (a : A) (t : ℝ≥0) (ht : t ≤ 1) :
    secondMoment (p a) (convexLaw t ht q₀ q₁) ≤
      (t : ℝ)*secondMoment (p a) q₀+(1-(t : ℝ))*secondMoment (p a) q₁ := by
  unfold secondMoment
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z _
  by_cases hp : mass (p a) z = 0
  · simp [hp]
  have hx : 0 < mass q₀ z := lt_of_le_of_ne (mass_nonneg _ _) (Ne.symm (hc₀ a z hp))
  have hy : 0 < mass q₁ z := lt_of_le_of_ne (mass_nonneg _ _) (Ne.symm (hc₁ a z hp))
  have hi := inverse_convex (mass q₀ z) (mass q₁ z) (t : ℝ) hx hy
    t.coe_nonneg (by exact_mod_cast ht)
  have hh := mul_le_mul_of_nonneg_left hi (sq_nonneg (mass (p a) z))
  convert hh using 1 <;> simp only [ratio, convexLaw_mass, div_eq_mul_inv] <;> ring

theorem mixture_convexLaw {A Z : Type*} (p : A → PMF Z) (eta₀ eta₁ : PMF A)
    (t : ℝ≥0) (ht : t ≤ 1) :
    mixture (convexLaw t ht eta₀ eta₁) p =
      convexLaw t ht (mixture eta₀ p) (mixture eta₁ p) := by
  simp only [convexLaw, mixture, PMF.bind_bind]
  congr 1
  funext b
  cases b <;> rfl

theorem designCost_convex {A Z : Type*} [Fintype A] [Nonempty A] [Fintype Z]
    (p : A → PMF Z) (eta₀ eta₁ : PMF A)
    (hc₀ : Covers p (mixture eta₀ p)) (hc₁ : Covers p (mixture eta₁ p))
    (t : ℝ≥0) (ht : t ≤ 1) :
    designCost p (convexLaw t ht eta₀ eta₁) ≤
      (t : ℝ)*designCost p eta₀+(1-(t : ℝ))*designCost p eta₁ := by
  apply Finset.sup'_le
  intro a _
  rw [mixture_convexLaw]
  refine (secondMoment_convex p _ _ hc₀ hc₁ a t ht).trans ?_
  exact add_le_add
    (mul_le_mul_of_nonneg_left (secondMoment_le_designCost p eta₀ a) t.coe_nonneg)
    (mul_le_mul_of_nonneg_left (secondMoment_le_designCost p eta₁ a)
      (sub_nonneg.mpr (by exact_mod_cast ht)))

theorem design_sublevel_mass_lower {A Z : Type*} [Fintype A] [Nonempty A] [Fintype Z]
    (p : A → PMF Z) (eta : PMF A) (hc : Covers p (mixture eta p))
    (K : ℝ) (hK : 0 < K) (hcost : designCost p eta ≤ K) (a : A) (z : Z) :
    mass (p a) z ^ 2 / K ≤ mass (mixture eta p) z := by
  by_cases hp : mass (p a) z = 0
  · simpa [hp] using mass_nonneg (mixture eta p) z
  have hq : 0 < mass (mixture eta p) z :=
    lt_of_le_of_ne (mass_nonneg _ _) (Ne.symm (hc a z hp))
  have hterm : mass (p a) z * ratio (p a) (mixture eta p) z ≤
      secondMoment (p a) (mixture eta p) :=
    Finset.single_le_sum (fun w _ => mul_nonneg (mass_nonneg (p a) w)
      (ratio_nonneg (p a) (mixture eta p) w)) (Finset.mem_univ z)
  have hbound := hterm.trans ((secondMoment_le_designCost p eta a).trans hcost)
  have hdiv : mass (p a) z ^ 2 / mass (mixture eta p) z ≤ K := by
    simpa [ratio, pow_two, mul_div_assoc] using hbound
  apply (div_le_iff₀ hK).mpr
  exact (div_le_iff₀ hq).mp hdiv |>.trans_eq (mul_comm _ _)

end BanditRLProof.Causal
