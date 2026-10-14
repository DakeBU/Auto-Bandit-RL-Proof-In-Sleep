import BanditRLProof.OnlineGuessingSubgradient
import BanditRLProof.OnlineSubgradientPolicy

noncomputable section
open Set Finset Filter BanditRL.OnlineConvex
open BanditRL.OnlineSubgradientPolicy
open BanditRL.OnlineGuessingSubgradient (loss loss_subgradient_bound loss_on_unitInterval)
open BanditRL.OnlineGradientDescent (unitInterval)
namespace BanditRL.OnlineGuessingSubgradientPolicy

/-!
Example2.32 in Orabona arXiv1912.13213v10, printed20/PDF32.
Reuse the shared absolute loss, unit interval and actual projected finite-history
policy recursion. Every played legal support is allowed, including historical
choices in the full tie interval. Performance uses this same eta=1/sqrtT run,
not a supplied regret inequality or a universal off-path oracle premise.
The exact finite sqrtT bound specializes the source OSD transfer at D=G=1.
The last theorem is only eventual upper average over separately prescribed
horizons, not signed convergence to zero or one anytime run.
Broader norm/clamp algebra permits arbitrary initialization/labels/rates;
the tuned source game retains feasible labels/initialization and positive T.
-/

theorem selected_bound (η : ℕ → ℝ) (y : ℕ → ℝ) (x₁ : ℝ)
    (p : SupportPolicy (E := ℝ)) (T : ℕ)
    (hlegal : LegalFeedback unitInterval η (fun s => loss (y s)) x₁ p T)
    (t : ℕ) (ht : t < T) :
    ‖selected unitInterval η (fun s => loss (y s)) x₁ p t‖ ≤ 1 := by
  exact loss_subgradient_bound (y t) _ _ (hlegal t ht)

theorem step_clamp (η : ℕ → ℝ) (y : ℕ → ℝ) (x₁ : ℝ)
    (p : SupportPolicy (E := ℝ)) (t : ℕ) :
    output unitInterval η (fun s => loss (y s)) x₁ p (t + 1) =
      min (max (output unitInterval η (fun s => loss (y s)) x₁ p t -
        η t * selected unitInterval η (fun s => loss (y s)) x₁ p t) 0) 1 := by
  simp only [output_succ, BanditRL.OnlineGradientDescent.project_unitInterval, smul_eq_mul]

theorem example_2_32 (y : ℕ → ℝ) (x₁ : ℝ) (p : SupportPolicy (E := ℝ))
    (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Icc (0 : ℝ) 1)
    (hlegal : LegalFeedback unitInterval (fun _ => 1 / Real.sqrt T)
      (fun s => loss (y s)) x₁ p T) :
    ∀ u ∈ Icc (0 : ℝ) 1,
      (∑ t ∈ range T,
        (|output unitInterval (fun _ => 1 / Real.sqrt T)
          (fun s => loss (y s)) x₁ p t - y t| - |u - y t|)) ≤ Real.sqrt T := by
  have hdiam : ∀ x ∈ unitInterval.carrier,
      ∀ z ∈ unitInterval.carrier, ‖x - z‖ ≤ (1 : ℝ) := by
    intro x hx z hz
    change x ∈ Icc (0 : ℝ) 1 at hx
    change z ∈ Icc (0 : ℝ) 1 at hz
    change |x - z| ≤ 1
    exact abs_le.mpr ⟨by linarith [hx.1, hz.2], by linarith [hx.2, hz.1]⟩
  have hlegal' : LegalFeedback unitInterval (fun _ => 1 / (1 * Real.sqrt T))
      (fun s => loss (y s)) x₁ p T := by
    simpa only [one_mul] using hlegal
  have hb := BanditRL.OnlineSubgradientPolicy.regret_tuned unitInterval
    (fun s => loss (y s)) x₁ p hx₁ T hT 1 1 (by norm_num) (by norm_num)
    (fun t ht => loss_on_unitInterval (y t)) hlegal' hdiam
    (fun t ht => by
      simpa only [one_mul] using
        selected_bound (fun _ => 1 / Real.sqrt T) y x₁ p T hlegal t ht)
  simpa only [BanditRL.OnlineSubgradientPolicy.regret, loss, EReal.toReal_coe, one_mul]
    using hb

theorem example_2_32_average_eventually (y : ℕ → ℝ) (x₁ : ℝ)
    (p : SupportPolicy (E := ℝ)) (hx₁ : x₁ ∈ Icc (0 : ℝ) 1)
    (hy : ∀ t, y t ∈ Icc (0 : ℝ) 1)
    (hlegal : ∀ T : ℕ, 0 < T → LegalFeedback unitInterval
      (fun _ => 1 / Real.sqrt T) (fun s => loss (y s)) x₁ p T)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop,
      (∑ t ∈ range T,
        (|output unitInterval (fun _ => 1 / Real.sqrt T)
          (fun s => loss (y s)) x₁ p t - y t| - |u - y t|)) / T < ε := by
  have hlimit : Tendsto (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hsmall := hlimit.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with T hsmall hT
  have ht : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hs : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr ht
  have hb := example_2_32 y x₁ p hx₁ T hT (fun t ht => hy t) (hlegal T hT) u hu
  calc
    (∑ t ∈ range T,
      (|output unitInterval (fun _ => 1 / Real.sqrt T)
        (fun s => loss (y s)) x₁ p t - y t| - |u - y t|)) / T ≤ Real.sqrt T / T :=
        div_le_div_of_nonneg_right hb (Nat.cast_nonneg T)
    _ = (Real.sqrt T)⁻¹ := by
      rw [inv_eq_one_div]
      apply (div_eq_div_iff (ne_of_gt ht) (ne_of_gt hs)).mpr
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg T)]
    _ < ε := hsmall

end BanditRL.OnlineGuessingSubgradientPolicy
