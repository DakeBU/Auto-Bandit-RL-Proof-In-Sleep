import BanditRLProof.OnlinePrescientBregmanRegret
import Tests.OnlinePrescientBregmanCanary
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman
namespace BanditRL.OnlinePrescientBregmanRegretCanary

theorem fixed_signed_run :
    let V : Set ℝ := Icc (-1) 1
    let ψ : ℝ → ℝ := fun z => z ^ 4 / 4 + z ^ 2 / 2
    let f0 : ℝ → EReal := fun z => if z ∈ V then ((|z| : ℝ) : EReal) else ⊤
    let f1 : ℝ → EReal := fun z => if z ∈ V then ((-5 * z / 8 : ℝ) : EReal) else ⊤
    let loss : ℕ → ℝ → EReal := fun t => if t = 0 then f0 else f1
    let x : ℕ → ℝ := fun t => if t = 1 then 0 else 1 / 2
    SourceProper f0 ∧ SourceProper f1 ∧
      (∀ z ∈ V, (SourceSubdifferential f0 z).Nonempty) ∧
      (∀ z ∈ V, (SourceSubdifferential f1 z).Nonempty) ∧
      SourceClosed (fun z => ((ψ z : ℝ) : EReal)) ∧
      StrictConvexOn ℝ univ ψ ∧ DifferentiableOn ℝ ψ univ ∧
      (∀ t ≤ 2, iterate V ψ (fun _ => 1) loss (1 / 2) t = some (x t)) ∧
      divergence ψ (-1 / 2) (x 2) = 5 / 8 ∧
      divergence ψ (x 1) (x 0) = 11 / 64 ∧
      divergence ψ (x 2) (x 1) = 9 / 64 ∧
      (∀ u ∈ V, (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        (∑ t ∈ range 2, (divergence ψ u (x t) - divergence ψ u (x (t + 1))) / 1) -
        ∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t) / 1) ∧
      (∀ u ∈ V, (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        divergence ψ u (1 / 2) / 1 - divergence ψ u (x 2) / 1 -
        (∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t)) / 1) ∧
      (∀ u ∈ V, (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        divergence ψ u (1 / 2) / 1 -
        (∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t)) / 1) ∧
      (-9 / 8 : ℝ) ≤ -5 / 16 ∧ (-9 / 8 : ℝ) ≤ 5 / 16 := by
  dsimp only
  let V : Set ℝ := Icc (-1) 1
  let ψ : ℝ → ℝ := fun z => z ^ 4 / 4 + z ^ 2 / 2
  let f0 : ℝ → EReal := fun z => if z ∈ V then ((|z| : ℝ) : EReal) else ⊤
  let f1 : ℝ → EReal := fun z => if z ∈ V then ((-5 * z / 8 : ℝ) : EReal) else ⊤
  let loss : ℕ → ℝ → EReal := fun t => if t = 0 then f0 else f1
  let x : ℕ → ℝ := fun t => if t = 1 then 0 else 1 / 2
  obtain ⟨hf0, hf1, hs0, hs1, hstrict, _, _, _, h0, h1, h2, _, hD10, hD01, _, _⟩ :=
    BanditRL.OnlinePrescientBregmanCanary.two_distinct_current_losses
  have hd (z : ℝ) : HasDerivAt ψ (z ^ 3 + z) z := by
    convert (((hasDerivAt_id z).pow 4).div_const 4).add
      (((hasDerivAt_id z).pow 2).div_const 2) using 1
    dsimp [ψ, id]
    ring
  have hD (a b : ℝ) : divergence ψ a b = ψ a - ψ b - (b ^ 3 + b) * (a - b) := by
    rw [divergence, fderiv_eq_deriv_mul, (hd b).deriv]
  have hdiff : DifferentiableOn ℝ ψ (interior (univ : Set ℝ)) := by
    simp only [interior_univ]
    intro z _
    exact (hd z).differentiableAt.differentiableWithinAt
  have hcont : Continuous ψ := (show Differentiable ℝ ψ from fun z => (hd z).differentiableAt).continuous
  have hclosed : SourceClosed (fun z => ((ψ z : ℝ) : EReal)) := by
    intro r
    change IsClosed {z : ℝ | (ψ z : EReal) ≤ (r : EReal)}
    simpa only [EReal.coe_le_coe_iff] using
      (isClosed_le hcont (continuous_const : Continuous (fun _ : ℝ => r)))
  have hseq : ∀ t ≤ 2, iterate V ψ (fun _ => 1) loss (1 / 2) t = some (x t) := by
    intro t ht
    have ht' : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases ht' with rfl | rfl | rfl
    · simpa [V, ψ, loss, f0, f1, x] using h0
    · simpa [V, ψ, loss, f0, f1, x] using h1
    · simpa [V, ψ, loss, f0, f1, x] using h2
  have hi : ∀ t ≤ 2, x t ∈ interior (univ : Set ℝ) := by simp
  have hf (t : ℕ) (_ : t < 2) : SourceProper (loss t) := by
    by_cases h : t = 0
    · simpa [loss, h, V, f0, f1] using hf0
    · simpa [loss, h, V, f0, f1] using hf1
  have hs (t : ℕ) (_ : t < 2) : ∀ z ∈ V, (SourceSubdifferential (loss t) z).Nonempty := by
    by_cases h : t = 0
    · simpa [loss, h, V, f0, f1] using hs0
    · simpa [loss, h, V, f0, f1] using hs1
  have hshared : ∀ u ∈ V,
      (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        (∑ t ∈ range 2, (divergence ψ u (x t) - divergence ψ u (x (t + 1))) / 1) -
        ∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t) / 1 := by
    intro u hu
    exact iterate_divergence_sum V univ (convex_Icc (-1 : ℝ) 1) ψ hdiff
      (fun _ => 1) loss (1 / 2) x 2 hseq hi (by intros; norm_num) hf hs u hu
  have hsharp : ∀ u ∈ V,
      (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        divergence ψ u (1 / 2) / 1 - divergence ψ u (x 2) / 1 -
        (∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t)) / 1 := by
    intro u hu
    exact iterate_fixed_sharp V univ (convex_Icc (-1 : ℝ) 1) ψ hdiff
      1 (by norm_num) loss (1 / 2) x 2 hseq hi hf hs u hu
  have hprinted : ∀ u ∈ V,
      (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        divergence ψ u (1 / 2) / 1 -
        (∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t)) / 1 := by
    intro u hu
    exact iterate_fixed_regret V univ (convex_Icc (-1 : ℝ) 1) (fun _ _ => mem_univ _)
      ψ hstrict hdiff 1 (by norm_num) loss (1 / 2) x 2 hseq hi hf hs u hu
  have hterminal : divergence ψ (-1 / 2) (x 2) = 5 / 8 := by
    rw [hD]
    norm_num [ψ, x]
  have hnumSharp : (-9 / 8 : ℝ) ≤ -5 / 16 := by
    convert hsharp (-1 / 2) (by norm_num [V]) using 1 <;>
      norm_num [sum_range_succ, loss, f0, f1, V, x, hD, ψ]
  have hnumPrinted : (-9 / 8 : ℝ) ≤ 5 / 16 := by
    convert hprinted (-1 / 2) (by norm_num [V]) using 1 <;>
      norm_num [sum_range_succ, loss, f0, f1, V, x, hD, ψ]
  refine ⟨hf0, hf1, hs0, hs1, hclosed, hstrict, ?_, hseq, hterminal, ?_, ?_,
    hshared, hsharp, hprinted, hnumSharp, hnumPrinted⟩
  · simpa only [interior_univ] using hdiff
  · simpa [x] using hD10
  · simpa [x] using hD01

end BanditRL.OnlinePrescientBregmanRegretCanary
