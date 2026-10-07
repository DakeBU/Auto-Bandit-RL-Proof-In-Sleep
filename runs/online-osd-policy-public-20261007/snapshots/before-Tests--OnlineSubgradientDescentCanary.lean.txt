import BanditRLProof.OnlineSubgradientDescent
import BanditRLProof.OnlineSubgradientAbsolute
import BanditRLProof.OnlineHinge

noncomputable section
/-! Actual arbitrary-current clipping and canonical absolute-loss trajectories.
No user-supplied step inequality, selected slope, trajectory or regret premise.
These fixtures exercise source boundaries; Example2.32 shifted game remains separate. -/
namespace OSDOutsideProbe
open Set BanditRL.OnlineConvex BanditRL.OnlineSubgradientDescent
def interval : BanditRL.OnlineGradientDescent.Domain ℝ where
  carrier := Icc (-1) 1
  nonempty := ⟨0, by norm_num⟩
  closed := isClosed_Icc
  convex := convex_Icc (-1) 1
def linearLoss (x : ℝ) : EReal := ((inner ℝ (3 : ℝ) x + 0 : ℝ) : EReal)
theorem linear_on : SubdifferentiableOn interval linearLoss := by
  refine ⟨affine_proper (3 : ℝ) 0, ?_⟩
  intro x hx
  refine ⟨3, ?_⟩
  change (3 : ℝ) ∈ SourceSubdifferential (fun y => ((inner ℝ (3 : ℝ) y + 0 : ℝ) : EReal)) x
  rw [affine_subdifferential]
  exact mem_singleton _
theorem support_at_two : (3 : ℝ) ∈ SourceSubdifferential linearLoss 2 := by
  change (3 : ℝ) ∈ SourceSubdifferential (fun y => ((inner ℝ (3 : ℝ) y + 0 : ℝ) : EReal)) 2
  rw [affine_subdifferential]
  exact mem_singleton _
theorem project_neg_four : BanditRL.OnlineGradientDescent.project interval (-4) = -1 := by
  apply BanditRL.OnlineGradientDescent.project_eq_of_variational interval (-4) (-1) (by norm_num [interval])
  intro w hw
  change w ∈ Icc (-1 : ℝ) 1 at hw
  change (w - (-1)) * ((-4 : ℝ) - (-1)) ≤ 0
  nlinarith [hw.1]
theorem arbitrary_current_and_actual_clipping :
    (2 : ℝ) ∉ interval.carrier ∧
    BanditRL.OnlineGradientDescent.project interval ((2 : ℝ) - (2 : ℝ) • (3 : ℝ)) = -1 ∧
    (2 * ((linearLoss 2).toReal - (linearLoss 0).toReal) ≤
      2 * inner ℝ (3 : ℝ) ((2 : ℝ) - 0) ∧
    2 * inner ℝ (3 : ℝ) ((2 : ℝ) - 0) ≤
      ‖(2 : ℝ) - 0‖ ^ 2 / 2 -
      ‖BanditRL.OnlineGradientDescent.project interval ((2 : ℝ) - (2 : ℝ) • (3 : ℝ)) - 0‖ ^ 2 / 2 +
      (2 : ℝ) ^ 2 / 2 * ‖(3 : ℝ)‖ ^ 2) := by
  refine ⟨by norm_num [interval], ?_, ?_⟩
  · simpa only [smul_eq_mul, show (2 : ℝ) - 2 * 3 = -4 by norm_num] using project_neg_four
  · exact lemma_2_31 interval linearLoss linear_on 2 (by norm_num) 2 0
      (by norm_num [interval]) 3 support_at_two
#print axioms arbitrary_current_and_actual_clipping
end OSDOutsideProbe

namespace OSDAlgorithmProbe
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineSubgradientDescent
open scoped InnerProductSpace
abbrev interval := OSDOutsideProbe.interval
def absoluteLoss (x : ℝ) : EReal := ((|x| : ℝ) : EReal)
def losses : ℕ → ℝ → EReal := fun _ => absoluteLoss

theorem absolute_on : SubdifferentiableOn interval absoluteLoss := by
  refine ⟨⟨fun _ => EReal.coe_ne_bot _, 0, 0, by simp [absoluteLoss]⟩, ?_⟩
  intro x hx
  change (SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) x).Nonempty
  by_cases hp : 0 < x
  · rw [abs_subgradient_positive x hp]
    exact singleton_nonempty 1
  · by_cases hz : x = 0
    · subst x
      rw [abs_subgradient_zero]
      exact ⟨0, by norm_num⟩
    · rw [abs_subgradient_negative x (lt_of_le_of_ne (le_of_not_gt hp) hz)]
      exact singleton_nonempty (-1)

theorem chosen_positive : currentSubgradient absoluteLoss (1 : ℝ) = 1 := by
  have hg := currentSubgradient_mem interval absoluteLoss absolute_on 1 (by norm_num [interval, OSDOutsideProbe.interval])
  change currentSubgradient absoluteLoss 1 ∈ SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) 1 at hg
  rw [abs_subgradient_positive 1 (by norm_num)] at hg
  exact hg

theorem chosen_negative : currentSubgradient absoluteLoss (-1 : ℝ) = -1 := by
  have hg := currentSubgradient_mem interval absoluteLoss absolute_on (-1) (by norm_num [interval, OSDOutsideProbe.interval])
  change currentSubgradient absoluteLoss (-1) ∈ SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) (-1) at hg
  rw [abs_subgradient_negative (-1) (by norm_num)] at hg
  exact hg

theorem chosen_norm (x : ℝ) (hx : x ∈ interval.carrier) :
    ‖currentSubgradient absoluteLoss x‖ ≤ 1 := by
  have hg := currentSubgradient_mem interval absoluteLoss absolute_on x hx
  change currentSubgradient absoluteLoss x ∈ SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) x at hg
  by_cases hp : 0 < x
  · rw [abs_subgradient_positive x hp] at hg
    have he : currentSubgradient absoluteLoss x = 1 := hg
    rw [he]; norm_num
  · by_cases hz : x = 0
    · subst x
      rw [abs_subgradient_zero] at hg
      change |currentSubgradient absoluteLoss 0| ≤ 1
      exact abs_le.mpr hg
    · rw [abs_subgradient_negative x (lt_of_le_of_ne (le_of_not_gt hp) hz)] at hg
      have he : currentSubgradient absoluteLoss x = -1 := hg
      rw [he]; norm_num

theorem project_neg_two : BanditRL.OnlineGradientDescent.project interval (-2 : ℝ) = -1 := by
  apply BanditRL.OnlineGradientDescent.project_eq_of_variational interval (-2) (-1) (by norm_num [interval, OSDOutsideProbe.interval])
  intro w hw
  change w ∈ Icc (-1 : ℝ) 1 at hw
  change (w - (-1)) * ((-2 : ℝ) - (-1)) ≤ 0
  nlinarith [hw.1]

theorem project_two : BanditRL.OnlineGradientDescent.project interval (2 : ℝ) = 1 := by
  apply BanditRL.OnlineGradientDescent.project_eq_of_variational interval 2 1 (by norm_num [interval, OSDOutsideProbe.interval])
  intro w hw
  change w ∈ Icc (-1 : ℝ) 1 at hw
  change (w - 1) * ((2 : ℝ) - 1) ≤ 0
  nlinarith [hw.2]

theorem project_one : BanditRL.OnlineGradientDescent.project interval (1 : ℝ) = 1 := by
  apply BanditRL.OnlineGradientDescent.project_eq_of_variational interval 1 1 (by norm_num [interval, OSDOutsideProbe.interval])
  intro w hw
  simp

theorem fixed_first : iterate interval (fun _ => (3 : ℝ)) losses 1 1 = -1 := by
  change BanditRL.OnlineGradientDescent.project interval (1 - (3 : ℝ) • currentSubgradient absoluteLoss 1) = -1
  rw [chosen_positive]
  simpa only [smul_eq_mul, show (1 : ℝ) - 3 * 1 = -2 by norm_num] using project_neg_two

theorem fixed_second : iterate interval (fun _ => (3 : ℝ)) losses 1 2 = 1 := by
  change step interval 3 absoluteLoss (iterate interval (fun _ => (3 : ℝ)) losses 1 1) = 1
  rw [fixed_first]
  unfold step
  rw [chosen_negative]
  simpa only [smul_eq_mul, show (-1 : ℝ) - 3 * (-1) = 2 by norm_num] using project_two

theorem fixed_clipped_two_round :
    iterate interval (fun _ => (3 : ℝ)) losses 1 0 = 1 ∧
    iterate interval (fun _ => (3 : ℝ)) losses 1 1 = -1 ∧
    iterate interval (fun _ => (3 : ℝ)) losses 1 2 = 1 ∧
    regret interval (fun _ => (3 : ℝ)) losses 1 0 2 = 2 ∧
    (1 : ℝ) - (3 : ℝ) • currentSubgradient absoluteLoss 1 = -2 ∧
    (-1 : ℝ) - (3 : ℝ) • currentSubgradient absoluteLoss (-1) = 2 := by
  refine ⟨rfl, fixed_first, fixed_second, ?_, ?_, ?_⟩
  · simp only [regret, sum_range_succ, sum_range_zero, zero_add, fixed_first]
    norm_num [iterate, losses, absoluteLoss]
  · rw [chosen_positive]; norm_num
  · rw [chosen_negative]; norm_num

theorem fixed_bound_with_terminal :
    regret interval (fun _ => (3 : ℝ)) losses 1 0 2 ≤
      ‖(1 : ℝ) - 0‖ ^ 2 / (2 * 3) +
      (3 : ℝ) / 2 * (∑ t ∈ range 2,
        ‖currentSubgradient (losses t) (iterate interval (fun _ => (3 : ℝ)) losses 1 t)‖ ^ 2) -
      ‖iterate interval (fun _ => (3 : ℝ)) losses 1 2 - 0‖ ^ 2 / (2 * 3) := by
  exact regret_fixed interval 3 (by norm_num) losses 1
    (by norm_num [interval, OSDOutsideProbe.interval]) 2 (fun t ht => absolute_on) 0
    (by norm_num [interval, OSDOutsideProbe.interval])

theorem fixed_terminal_positive :
    ‖iterate interval (fun _ => (3 : ℝ)) losses 1 2 - 0‖ ^ 2 / (2 * 3) = (1 : ℝ) / 6 := by
  rw [fixed_second]; norm_num

def variableEta (t : ℕ) : ℝ := if t = 0 then 3 else 2

theorem variable_first : iterate interval variableEta losses 1 1 = -1 := by
  change step interval (variableEta 0) absoluteLoss 1 = -1
  simpa only [iterate, losses, variableEta, if_pos rfl] using fixed_first

theorem variable_second : iterate interval variableEta losses 1 2 = 1 := by
  change step interval (variableEta 1) absoluteLoss (iterate interval variableEta losses 1 1) = 1
  rw [variable_first]
  simp only [variableEta, if_neg (by omega : (1 : ℕ) ≠ 0), step, chosen_negative, smul_eq_mul]
  convert project_one using 1 <;> norm_num

theorem diameter_two : ∀ x ∈ interval.carrier, ∀ y ∈ interval.carrier, ‖x - y‖ ≤ (2 : ℝ) := by
  intro x hx y hy
  change x ∈ Icc (-1 : ℝ) 1 at hx
  change y ∈ Icc (-1 : ℝ) 1 at hy
  change |x - y| ≤ 2
  exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

theorem variable_bound_with_terminal :
    regret interval variableEta losses 1 0 2 ≤ (2 : ℝ) ^ 2 / (2 * variableEta (2 - 1)) +
      (∑ t ∈ range 2, variableEta t / 2 *
        ‖currentSubgradient (losses t) (iterate interval variableEta losses 1 t)‖ ^ 2) -
      ‖iterate interval variableEta losses 1 2 - 0‖ ^ 2 / (2 * variableEta (2 - 1)) := by
  apply regret_variable_bound interval variableEta losses 1
    (by norm_num [interval, OSDOutsideProbe.interval]) 2 (by omega)
    (fun t ht => by unfold variableEta; split_ifs <;> norm_num)
    (fun t ht => by
      have he : t = 0 := by omega
      subst t
      norm_num [variableEta])
    (fun t ht => absolute_on) 2 diameter_two 0 (by norm_num [interval, OSDOutsideProbe.interval])

theorem variable_nonconstant_and_terminal :
    variableEta 0 = 3 ∧ variableEta 1 = 2 ∧
    iterate interval variableEta losses 1 1 = -1 ∧
    iterate interval variableEta losses 1 2 = 1 ∧
    ‖iterate interval variableEta losses 1 2 - 0‖ ^ 2 / (2 * variableEta (2 - 1)) = (1 : ℝ) / 4 := by
  refine ⟨by norm_num [variableEta], by norm_num [variableEta], variable_first, variable_second, ?_⟩
  rw [variable_second]; norm_num [variableEta]

theorem tuned_all_comparators (T : ℕ) (hT : 0 < T) :
    ∀ u ∈ interval.carrier,
      regret interval (fun _ => (2 : ℝ) / (1 * Real.sqrt T)) losses 1 u T ≤
        2 * 1 * Real.sqrt T := by
  apply regret_tuned interval losses 1 (by norm_num [interval, OSDOutsideProbe.interval])
    T hT 2 1 (by norm_num) (by norm_num) diameter_two (fun t ht => absolute_on)
  intro t ht
  exact chosen_norm _ (iterate_mem interval _ losses 1 (by norm_num [interval, OSDOutsideProbe.interval]) t)

def futureEta (s : ℕ) : ℝ := if s < 2 then 3 else -99
def futureLoss (s : ℕ) : ℝ → EReal := if s < 2 then absoluteLoss else fun _ => ⊤

theorem future_inputs_do_not_change_output : iterate interval futureEta futureLoss 1 2 = 1 := by
  have he := iterate_prefix interval (fun _ => (3 : ℝ)) futureEta losses futureLoss 1 2
    (fun s hs => by simp [futureEta, hs]) (fun s hs => by simp [futureLoss, losses, hs])
  rw [← he]
  exact fixed_second

theorem zero_horizon : regret interval (fun _ => (3 : ℝ)) losses 1 0 0 = 0 ∧
    regret interval (fun _ => (3 : ℝ)) losses 1 0 0 ≤
      ‖(1 : ℝ) - 0‖ ^ 2 / (2 * 3) + (3 : ℝ) / 2 *
        (∑ t ∈ range 0, ‖currentSubgradient (losses t) (iterate interval (fun _ => (3 : ℝ)) losses 1 t)‖ ^ 2) -
      ‖iterate interval (fun _ => (3 : ℝ)) losses 1 0 - 0‖ ^ 2 / (2 * 3) := by
  refine ⟨by simp [regret], ?_⟩
  exact regret_fixed interval 3 (by norm_num) losses 1
    (by norm_num [interval, OSDOutsideProbe.interval]) 0 (fun t ht => by omega) 0
    (by norm_num [interval, OSDOutsideProbe.interval])

#print axioms absolute_on
#print axioms chosen_norm
#print axioms fixed_clipped_two_round
#print axioms fixed_bound_with_terminal
#print axioms fixed_terminal_positive
#print axioms variable_bound_with_terminal
#print axioms variable_nonconstant_and_terminal
#print axioms tuned_all_comparators
#print axioms future_inputs_do_not_change_output
#print axioms zero_horizon
end OSDAlgorithmProbe
