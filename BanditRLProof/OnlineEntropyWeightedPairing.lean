import Mathlib.Analysis.Convex.Mul
import BanditRLProof.OnlineEntropyScalarGap
import Mathlib.Analysis.Convex.Jensen

noncomputable section
open Finset
namespace BanditRL.OnlineEntropy

def weightedEntropy {d : ℕ} (c x : Fin d → ℝ) : ℝ :=
  ∑ i, c i * x i * Real.log (x i)

def weightedSimplex {d : ℕ} (c : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i / c i = 1}

theorem weightedEntropy_differential {d : ℕ} (c x : Fin d → ℝ)
    (hx : ∀ i, 0 < x i) :
    DifferentiableAt ℝ (weightedEntropy c) x ∧
    ∀ v : Fin d → ℝ, fderiv ℝ (weightedEntropy c) x v =
      ∑ i, c i * (Real.log (x i) + 1) * v i := by
  let L (i : Fin d) := (c i * (Real.log (x i) + 1)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i
  have hi (i : Fin d) : HasFDerivAt (fun a : Fin d → ℝ => c i * a i * Real.log (a i)) (L i) x := by
    have hs := ((hasDerivAt_id (x i)).const_mul (c i)).mul (Real.hasDerivAt_log (hx i).ne')
    have hh : HasDerivAt (fun t : ℝ => c i * t * Real.log t) (c i * (Real.log (x i)+1)) (x i) := by
      convert hs using 1 <;> first | rfl | (dsimp; field_simp [(hx i).ne'] <;> ring)
    exact HasDerivAt.comp_hasFDerivAt (f := fun a : Fin d → ℝ => a i) x hh (hasFDerivAt_apply i x)
  have h : HasFDerivAt (weightedEntropy c) (∑ i, L i) x := HasFDerivAt.fun_sum (fun i _ => hi i)
  refine ⟨h.differentiableAt,fun v => ?_⟩
  rw [h.fderiv];simp [L, ContinuousLinearMap.sum_apply]

theorem weightedEntropy_pairing {d : ℕ} (c x y : Fin d → ℝ)
    (hc : ∀ i, 0 < c i) (hx : x ∈ weightedSimplex c) (hy : y ∈ weightedSimplex c) :
    (∑ i, |x i - y i|)^2 ≤ ∑ i, 2 * c i * (x i - y i)^2 / (x i + y i) ∧
    (∑ i, 2 * c i * (x i - y i)^2 / (x i + y i)) ≤
      (fderiv ℝ (weightedEntropy c) x - fderiv ℝ (weightedEntropy c) y) (x-y) := by
  let w (i : Fin d) := (x i+y i)/(2*c i)
  let z (i : Fin d) := |x i-y i|/w i
  have hw (i : Fin d) : 0 < w i := div_pos (add_pos (hx.1 i) (hy.1 i)) (mul_pos (by norm_num) (hc i))
  have hsum : ∑ i, w i = 1 := by
    calc
      _ = ∑ i, (x i/c i+y i/c i)/2 := by
        apply Finset.sum_congr rfl;intro i _;dsimp [w];ring
      _ = (∑ i, (x i/c i+y i/c i)) * (2:ℝ)⁻¹ := by rw [Finset.sum_mul]; rfl
      _ = _ := by rw [Finset.sum_add_distrib,hx.2,hy.2];norm_num
  constructor
  · have hj := (convexOn_pow (𝕜 := ℝ) 2).map_sum_le (t := Finset.univ) (p := z)
          (fun i _ => (hw i).le) hsum (fun i _ => show 0 ≤ z i from div_nonneg (abs_nonneg _) (hw i).le)
    simp only [smul_eq_mul] at hj
    have hl (i : Fin d) : w i*z i = |x i-y i| := by unfold z;field_simp [(hw i).ne']
    have hr (i : Fin d) : w i*z i^2 = 2*c i*(x i-y i)^2/(x i+y i) := by
      dsimp [z,w];rw [div_pow,sq_abs];field_simp [(hc i).ne',(add_pos (hx.1 i) (hy.1 i)).ne']
    simpa only [hl,hr] using hj
  · rw [ContinuousLinearMap.sub_apply,(weightedEntropy_differential c x hx.1).2,
        (weightedEntropy_differential c y hy.1).2,← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum;intro i _
    have h := mul_le_mul_of_nonneg_left (positive_pair_log_ratio (x i) (y i) (hx.1 i) (hy.1 i)).1 (hc i).le
    change _ ≤ c i * (Real.log (x i)+1) * (x i-y i) - c i*(Real.log (y i)+1)*(x i-y i)
    convert h using 1 <;> ring

end BanditRL.OnlineEntropy
