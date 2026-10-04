/- Source card: ONLINE-GUESSING-OSD-ORABONA-V10-2.32. Metadata-only native fence provenance marker; frozen mathematics and eight proof bodies unchanged. -/
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


end BanditRL.OnlineGuessingSubgradient
#print axioms BanditRL.OnlineGuessingSubgradient.loss_subdifferential_translate
#print axioms BanditRL.OnlineGuessingSubgradient.loss_subgradient_positive
#print axioms BanditRL.OnlineGuessingSubgradient.loss_subgradient_zero
#print axioms BanditRL.OnlineGuessingSubgradient.loss_subgradient_negative
#print axioms BanditRL.OnlineGuessingSubgradient.example_2_32_subdifferential
#print axioms BanditRL.OnlineGuessingSubgradient.loss_on_unitInterval
#print axioms BanditRL.OnlineGuessingSubgradient.loss_subgradient_bound
#print axioms BanditRL.OnlineGuessingSubgradient.current_subgradient_bound
