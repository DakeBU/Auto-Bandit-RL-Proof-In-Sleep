import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Finite gap layer-cake identities and a refined integral envelope. -/
namespace BanditRLProof.FiniteGapLayerCake
open MeasureTheory
set_option autoImplicit false

theorem intervalIntegrable_step (d a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => if x≤d then (1:ℝ) else 0) volume a b := by
  have h : Antitone (fun x : ℝ => if x≤d then (1:ℝ) else 0) := by
    intro x y hxy
    dsimp only
    split_ifs <;> simp_all
    linarith
  exact h.intervalIntegrable

theorem integral_step {a b d : ℝ} (hd : d∈Set.Icc a b) :
    (∫x in a..b, if x≤d then (1:ℝ) else 0)=d-a := by
  change (∫x in a..b, Set.indicator {x | x≤d} (fun _ => (1:ℝ)) x)=d-a
  rw [intervalIntegral.integral_indicator hd, intervalIntegral.integral_const]
  simp

theorem intervalIntegrable_card {ι : Type*} (s : Finset ι) (d : ι → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun x => ((s.filter (fun t => x≤d t)).card:ℝ)) volume a b := by
  classical
  convert
    (IntervalIntegrable.sum s (fun t _ => intervalIntegrable_step (d t) a b)) using 1
  funext x
  simp

theorem sum_eq_layerCake {ι : Type*} (s : Finset ι) (d : ι → ℝ) (a b : ℝ)
    (hd : ∀t∈s, d t∈Set.Icc a b) :
    ∑t∈s, d t = a*(s.card:ℝ)+(∫x in a..b, ((s.filter (fun t => x≤d t)).card:ℝ)) := by
  classical
  have he : (fun x => ((s.filter (fun t => x≤d t)).card:ℝ))=
      fun x => ∑t∈s, if x≤d t then (1:ℝ) else 0 := by funext x; simp
  rw [he, intervalIntegral.integral_finset_sum (fun t _ => intervalIntegrable_step (d t) a b)]
  have hs : (∑t∈s, ∫x in a..b, if x≤d t then (1:ℝ) else 0)=∑t∈s, (d t-a) :=
    Finset.sum_congr rfl (fun t ht => integral_step (hd t ht))
  rw [hs, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem sum_le_refined_integral {ι : Type*} (s : Finset ι) (d : ι → ℝ) (a b : ℝ)
    (ha : 0≤a) (hab : a≤b) (hd : ∀t∈s, d t∈Set.Icc a b)
    (ell : ℝ → ℝ) (hi : IntervalIntegrable ell volume a b)
    (hc : ∀x∈Set.Icc a b, ((s.filter (fun t => x≤d t)).card:ℝ)≤ell x+1) :
    ∑t∈s, d t ≤ a*ell a+(∫x in a..b, ell x)+b := by
  classical
  have he : s.filter (fun t => a≤d t)=s := Finset.filter_true_of_mem (fun t ht => (hd t ht).1)
  have hcard := hc a ⟨le_rfl,hab⟩
  rw [he] at hcard
  have hmul := mul_le_mul_of_nonneg_left hcard ha
  have hint := intervalIntegral.integral_mono_on hab (intervalIntegrable_card s d a b)
    (hi.add intervalIntegrable_const) hc
  rw [intervalIntegral.integral_add hi intervalIntegrable_const,
    intervalIntegral.integral_const] at hint
  simp only [smul_eq_mul, mul_one] at hint
  rw [sum_eq_layerCake s d a b hd]
  nlinarith

end BanditRLProof.FiniteGapLayerCake
