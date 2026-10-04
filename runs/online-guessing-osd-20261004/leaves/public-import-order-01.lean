/-!
# Absolute-loss guessing by causal projected OSD
Orabona arXiv:1912.13213v10, Example 2.32, printed20/PDF32.
Source card ONLINE-GUESSING-OSD-ORABONA-V10-2.32.
Full translated global support sets reuse the shared absolute-value equalities;
properness and all-support norm bounds feed the actual current-choice OSD run.
The same shared nearest projection clamps to [0,1]. Output index0 is source x1.
A single horizon-prescribed eta=1/sqrtT run gives real absolute regret <=sqrtT
for every feasible comparator. The eventual corollary is one-sided upper control
across separately prescribed horizons, not signed convergence or an anytime rule.
The noncomputable canonical choice is one permitted support rule; arbitrary
legal/history-adaptive support-family coverage and whole Chapter2/book remain
separate required obligations. No numerical zero tie rule is assumed.
-/
import BanditRLProof.OnlineSubgradientDescent
import BanditRLProof.OnlineSubgradientAbsolute
import BanditRLProof.OnlineGuessingOGD

noncomputable section
open Set Finset Filter BanditRL.OnlineConvex
open BanditRL.OnlineSubgradientDescent
namespace BanditRL.OnlineGuessingSubgradient

def loss (y x : ℝ) : EReal := ((|x - y| : ℝ) : EReal)

theorem loss_subdifferential_translate (y x : ℝ) :
    SourceSubdifferential (loss y) x =
      SourceSubdifferential (fun z : ℝ => ((|z| : ℝ) : EReal)) (x - y) := by
  ext g
  constructor
  · intro hg z
    have h := hg (z + y)
    simpa only [loss, add_sub_cancel_right,
      show (z + y) - x = z - (x - y) by ring] using h
  · intro hg z
    have h := hg (z - y)
    simpa only [loss, show (z - y) - (x - y) = z - x by ring] using h

theorem loss_subgradient_positive (y x : ℝ) (hxy : y < x) :
    SourceSubdifferential (loss y) x = {(1 : ℝ)} := by
  rw [loss_subdifferential_translate]
  exact abs_subgradient_positive (x - y) (sub_pos.mpr hxy)

theorem loss_subgradient_zero (y : ℝ) :
    SourceSubdifferential (loss y) y = Icc (-1 : ℝ) 1 := by
  rw [loss_subdifferential_translate, sub_self]
  exact abs_subgradient_zero

theorem loss_subgradient_negative (y x : ℝ) (hxy : x < y) :
    SourceSubdifferential (loss y) x = {(-1 : ℝ)} := by
  rw [loss_subdifferential_translate]
  exact abs_subgradient_negative (x - y) (sub_neg.mpr hxy)

theorem example_2_32_subdifferential (y x : ℝ) :
    SourceSubdifferential (loss y) x =
      if y < x then {(1 : ℝ)} else if x = y then Icc (-1 : ℝ) 1 else {(-1 : ℝ)} := by
  split_ifs with hxy he
  · exact loss_subgradient_positive y x hxy
  · subst x
    exact loss_subgradient_zero y
  · exact loss_subgradient_negative y x (lt_of_le_of_ne (le_of_not_gt hxy) he)

theorem loss_on_unitInterval (y : ℝ) :
    SubdifferentiableOn BanditRL.OnlineGradientDescent.unitInterval (loss y) := by
  refine ⟨⟨fun x => EReal.coe_ne_bot _, y, 0, by simp [loss]⟩, ?_⟩
  intro x hx
  by_cases hp : y < x
  · rw [loss_subgradient_positive y x hp]
    exact singleton_nonempty 1
  · by_cases he : x = y
    · subst x
      rw [loss_subgradient_zero]
      exact ⟨0, by norm_num⟩
    · rw [loss_subgradient_negative y x (lt_of_le_of_ne (le_of_not_gt hp) he)]
      exact singleton_nonempty (-1)

theorem loss_subgradient_bound (y x g : ℝ)
    (hg : g ∈ SourceSubdifferential (loss y) x) : ‖g‖ ≤ 1 := by
  by_cases hp : y < x
  · rw [loss_subgradient_positive y x hp] at hg
    have he : g = 1 := hg
    rw [he]; norm_num
  · by_cases he : x = y
    · subst x
      rw [loss_subgradient_zero] at hg
      change |g| ≤ 1
      exact abs_le.mpr hg
    · rw [loss_subgradient_negative y x (lt_of_le_of_ne (le_of_not_gt hp) he)] at hg
      have he : g = -1 := hg
      rw [he]; norm_num

theorem current_subgradient_bound (y x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) : ‖currentSubgradient (loss y) x‖ ≤ 1 := by
  exact loss_subgradient_bound y x (currentSubgradient (loss y) x)
    (currentSubgradient_mem BanditRL.OnlineGradientDescent.unitInterval (loss y)
      (loss_on_unitInterval y) x hx)


theorem loss_step_clamp (η y x : ℝ) :
    step BanditRL.OnlineGradientDescent.unitInterval η (loss y) x =
      min (max (x - η * currentSubgradient (loss y) x) 0) 1 := by
  simp only [step, BanditRL.OnlineGradientDescent.project_unitInterval, smul_eq_mul]

theorem guessing_prefix (η η' : ℕ → ℝ) (y y' : ℕ → ℝ) (x₁ : ℝ) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hy : ∀ s < t, y s = y' s) :
    iterate BanditRL.OnlineGradientDescent.unitInterval η (fun s => loss (y s)) x₁ t =
      iterate BanditRL.OnlineGradientDescent.unitInterval η' (fun s => loss (y' s)) x₁ t := by
  exact iterate_prefix BanditRL.OnlineGradientDescent.unitInterval η η'
    (fun s => loss (y s)) (fun s => loss (y' s)) x₁ t hη
    (fun s hs => congrArg loss (hy s hs))

theorem example_2_32 (y : ℕ → ℝ) (x₁ : ℝ) (hx₁ : x₁ ∈ Icc (0 : ℝ) 1)
    (T : ℕ) (hT : 0 < T) (hy : ∀ t < T, y t ∈ Icc (0 : ℝ) 1) :
    ∀ u ∈ Icc (0 : ℝ) 1,
      (∑ t ∈ range T,
        (|iterate BanditRL.OnlineGradientDescent.unitInterval (fun _ => 1 / Real.sqrt T)
          (fun s => loss (y s)) x₁ t - y t| - |u - y t|)) ≤ Real.sqrt T := by
  have hdiam : ∀ x ∈ BanditRL.OnlineGradientDescent.unitInterval.carrier,
      ∀ z ∈ BanditRL.OnlineGradientDescent.unitInterval.carrier, ‖x - z‖ ≤ (1 : ℝ) := by
    intro x hx z hz
    change x ∈ Icc (0 : ℝ) 1 at hx
    change z ∈ Icc (0 : ℝ) 1 at hz
    change |x - z| ≤ 1
    exact abs_le.mpr ⟨by linarith [hx.1, hz.2], by linarith [hx.2, hz.1]⟩
  have hb := regret_tuned BanditRL.OnlineGradientDescent.unitInterval
    (fun t => loss (y t)) x₁ hx₁ T hT 1 1 (by norm_num) (by norm_num) hdiam
    (fun t ht => loss_on_unitInterval (y t))
    (fun t ht => current_subgradient_bound (y t) _
      (iterate_mem BanditRL.OnlineGradientDescent.unitInterval _ _ x₁ hx₁ t))
  simpa only [regret, loss, EReal.toReal_coe, one_mul] using hb

theorem example_2_32_average_eventually (y : ℕ → ℝ) (x₁ : ℝ)
    (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (hy : ∀ t, y t ∈ Icc (0 : ℝ) 1)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop,
      (∑ t ∈ range T,
        (|iterate BanditRL.OnlineGradientDescent.unitInterval (fun _ => 1 / Real.sqrt T)
          (fun s => loss (y s)) x₁ t - y t| - |u - y t|)) / T < ε := by
  have hlimit : Tendsto (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hsmall := hlimit.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with T hsmall hT
  have ht : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hs : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr ht
  have hb := example_2_32 y x₁ hx₁ T hT (fun t ht => hy t) u hu
  calc
    (∑ t ∈ range T,
      (|iterate BanditRL.OnlineGradientDescent.unitInterval (fun _ => 1 / Real.sqrt T)
        (fun s => loss (y s)) x₁ t - y t| - |u - y t|)) / T ≤ Real.sqrt T / T :=
        div_le_div_of_nonneg_right hb (Nat.cast_nonneg T)
    _ = (Real.sqrt T)⁻¹ := by
      rw [inv_eq_one_div]
      apply (div_eq_div_iff (ne_of_gt ht) (ne_of_gt hs)).mpr
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg T)]
    _ < ε := hsmall


end BanditRL.OnlineGuessingSubgradient
