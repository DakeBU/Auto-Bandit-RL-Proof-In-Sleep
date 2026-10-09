import BanditRLProof.OnlinePrescientBregman
import BanditRLProof.OnlineGradientDescentVariable

noncomputable section
open Set Finset
namespace BanditRL.OnlinePrescientBregman
open BanditRL.OnlineBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem iterate_divergence_sum (V X : Set E) (hV : Convex ℝ V) (ψ : E → ℝ)
    (hd : DifferentiableOn ℝ ψ (interior X)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ)
    (hseq : ∀ t ≤ T, iterate V ψ η loss x0 t = some (x t))
    (hinterior : ∀ t ≤ T, x t ∈ interior X)
    (hη : ∀ t < T, 0 < η t)
    (hf : ∀ t < T, BanditRL.OnlineConvex.SourceProper (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (u : E) (hu : u ∈ V) :
    (∑ t ∈ range T, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      (∑ t ∈ range T, (divergence ψ u (x t) - divergence ψ u (x (t + 1))) / η t) -
      ∑ t ∈ range T, divergence ψ (x (t + 1)) (x t) / η t := by
  have hstep (t : ℕ) (ht : t ∈ range T) :
      (loss t (x (t + 1))).toReal - (loss t u).toReal ≤
        (divergence ψ u (x t) - divergence ψ u (x (t + 1))) / η t -
          divergence ψ (x (t + 1)) (x t) / η t := by
    have hlt : t < T := mem_range.mp ht
    have hle : t + 1 ≤ T := Nat.succ_le_of_lt hlt
    have a := iterate_one_step V hV ψ η loss x0 (x t) (x (t + 1)) t
      (hseq t (Nat.le_of_lt hlt)) (hseq (t + 1) hle) (hη t hlt)
      (hf t hlt) (hs t hlt)
      (hd.differentiableAt (isOpen_interior.mem_nhds (hinterior t (Nat.le_of_lt hlt))))
      (hd.differentiableAt (isOpen_interior.mem_nhds (hinterior (t + 1) hle))) u hu
    rw [← sub_div]
    apply (le_div_iff₀ (hη t hlt)).mpr
    simpa only [mul_comm] using a
  have hsum := Finset.sum_le_sum (s := range T) hstep
  simpa only [sum_sub_distrib] using hsum

theorem iterate_fixed_sharp (V X : Set E) (hV : Convex ℝ V) (ψ : E → ℝ)
    (hd : DifferentiableOn ℝ ψ (interior X)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ)
    (hseq : ∀ t ≤ T, iterate V ψ (fun _ => η) loss x0 t = some (x t))
    (hinterior : ∀ t ≤ T, x t ∈ interior X)
    (hf : ∀ t < T, BanditRL.OnlineConvex.SourceProper (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (u : E) (hu : u ∈ V) :
    (∑ t ∈ range T, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      divergence ψ u x0 / η - divergence ψ u (x T) / η -
      (∑ t ∈ range T, divergence ψ (x (t + 1)) (x t)) / η := by
  have h := iterate_divergence_sum V X hV ψ hd (fun _ => η) loss x0 x T
    hseq hinterior (fun _ _ => hη) hf hs u hu
  have hx : x 0 = x0 := (Option.some.inj (hseq 0 (Nat.zero_le T))).symm
  simpa only [← sum_div, sum_range_sub', hx, sub_div] using h

theorem iterate_variable_sharp (V X : Set E) (hV : Convex ℝ V) (ψ : E → ℝ)
    (hd : DifferentiableOn ℝ ψ (interior X)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ) (hT : 0 < T)
    (hseq : ∀ t ≤ T, iterate V ψ η loss x0 t = some (x t))
    (hinterior : ∀ t ≤ T, x t ∈ interior X)
    (hη : ∀ t < T, 0 < η t)
    (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hf : ∀ t < T, BanditRL.OnlineConvex.SourceProper (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (u : E) (hu : u ∈ V) (M : ℝ)
    (hbound : ∀ t < T, divergence ψ u (x t) ≤ M) :
    (∑ t ∈ range T, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      M / η (T - 1) - divergence ψ u (x T) / η (T - 1) -
      ∑ t ∈ range T, divergence ψ (x (t + 1)) (x t) / η t := by
  have hsum := iterate_divergence_sum V X hV ψ hd η loss x0 x T
    hseq hinterior hη hf hs u hu
  have hp := BanditRL.OnlineGradientDescent.weighted_potential_sum
    (fun t => 2 * divergence ψ u (x t)) η (2 * M) T hT hη hmono
    (fun t ht => mul_le_mul_of_nonneg_left (hbound t ht) (by norm_num))
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  simp only [← mul_sub, mul_div_mul_left _ _ htwo] at hp
  exact hsum.trans (sub_le_sub_right hp _)

theorem iterate_fixed_regret (V X : Set E) (hV : Convex ℝ V) (hVX : V ⊆ X)
    (ψ : E → ℝ) (hc : StrictConvexOn ℝ X ψ)
    (hd : DifferentiableOn ℝ ψ (interior X)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ)
    (hseq : ∀ t ≤ T, iterate V ψ (fun _ => η) loss x0 t = some (x t))
    (hinterior : ∀ t ≤ T, x t ∈ interior X)
    (hf : ∀ t < T, BanditRL.OnlineConvex.SourceProper (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (u : E) (hu : u ∈ V) :
    (∑ t ∈ range T, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      divergence ψ u x0 / η -
      (∑ t ∈ range T, divergence ψ (x (t + 1)) (x t)) / η := by
  have h := iterate_fixed_sharp V X hV ψ hd η hη loss x0 x T
    hseq hinterior hf hs u hu
  have hterminal := divergence_nonneg X ψ hc.convexOn u (x T) (hVX hu)
    (interior_subset (hinterior T le_rfl))
    (hd.differentiableAt (isOpen_interior.mem_nhds (hinterior T le_rfl)))
  have hquot : 0 ≤ divergence ψ u (x T) / η := div_nonneg hterminal hη.le
  linarith only [h, hquot]

end BanditRL.OnlinePrescientBregman
