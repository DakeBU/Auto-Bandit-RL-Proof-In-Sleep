import BanditRLProof.OnlineSubgradientPolicy
import BanditRLProof.OnlineGuessingSubgradient

/-! Actual history-sensitive legal feedback: identical current loss/current point
at time1, opposite chosen supports because the first past constant loss differs.
The flat round preserves the common point; later nonzero supports move it. -/
noncomputable section
namespace OSDPolicyProbe
open Set Finset BanditRL.OnlineConvex
open BanditRL.OnlineSubgradientPolicy
open BanditRL.OnlineGuessingSubgradient
abbrev V := BanditRL.OnlineGradientDescent.unitInterval
def flat (c x : ℝ) : EReal := (c : EReal)
def preferred (t : ℕ) (past : Fin t → ℝ → EReal) : ℝ :=
  if ht : 0 < t then if (past ⟨0, ht⟩ 0).toReal = 0 then 1 else -1 else 0
def policy : SupportPolicy (E := ℝ) := by
  classical
  exact fun t past h f =>
    if preferred t past ∈ SourceSubdifferential f (h (Fin.last t)) then preferred t past
    else BanditRL.OnlineSubgradientDescent.currentSubgradient f (h (Fin.last t))
def lossA (t : ℕ) : ℝ → EReal := if t = 0 then flat 0 else loss (1 / 2)
def lossB (t : ℕ) : ℝ → EReal := if t = 0 then flat 1 else loss (1 / 2)
def eta : ℕ → ℝ := fun _ => 1 / 2
abbrev a (t : ℕ) : ℝ := output V eta lossA (1 / 2) policy t
abbrev b (t : ℕ) : ℝ := output V eta lossB (1 / 2) policy t
abbrev ga (t : ℕ) : ℝ := selected V eta lossA (1 / 2) policy t
abbrev gb (t : ℕ) : ℝ := selected V eta lossB (1 / 2) policy t

theorem flat_on (c : ℝ) : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (flat c) := by
  constructor
  · refine ⟨?_, 0, c, rfl⟩
    intro x; simp [flat]
  · intro x hx
    refine ⟨0, ?_⟩
    simp [SourceSubdifferential, flat]

theorem policy_oracle : OracleLaw V policy := by
  classical
  intro t past h f hf hx
  change (if preferred t past ∈ SourceSubdifferential f (h (Fin.last t)) then
    preferred t past else BanditRL.OnlineSubgradientDescent.currentSubgradient f (h (Fin.last t))) ∈ _
  split_ifs with hg
  · exact hg
  · exact BanditRL.OnlineSubgradientDescent.currentSubgradient_mem V f hf _ hx

theorem lossA_on (t : ℕ) : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (lossA t) := by
  unfold lossA; split_ifs
  · exact flat_on 0
  · exact loss_on_unitInterval _

theorem lossB_on (t : ℕ) : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (lossB t) := by
  unfold lossB; split_ifs
  · exact flat_on 1
  · exact loss_on_unitInterval _

theorem pref_A (t : ℕ) (ht : 0 < t) : preferred t (fun i => lossA i.val) = 1 := by
  simp [preferred, ht, lossA, flat]

theorem pref_B (t : ℕ) (ht : 0 < t) : preferred t (fun i => lossB i.val) = -1 := by
  simp [preferred, ht, lossB, flat]

theorem selected_eq_preferred (η : ℕ → ℝ) (f : ℕ → ℝ → EReal) (t : ℕ)
    (hg : preferred t (fun i => f i.val) ∈ SourceSubdifferential (f t)
      (output V η f (1 / 2) policy t)) :
    selected V η f (1 / 2) policy t = preferred t (fun i => f i.val) := by
  classical
  change (if preferred t (fun i => f i.val) ∈ SourceSubdifferential (f t)
    (output V η f (1 / 2) policy t) then _ else _) = _
  rw [if_pos hg]

theorem selected_singleton (η : ℕ → ℝ) (f : ℕ → ℝ → EReal) (t : ℕ)
    (hf : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (f t))
    (g : ℝ) (hs : SourceSubdifferential (f t) (output V η f (1 / 2) policy t) = {g}) :
    selected V η f (1 / 2) policy t = g := by
  have hg := policy_oracle t (fun i => f i.val) (history V η f (1 / 2) policy t) (f t)
    hf (output_mem V η f (1 / 2) policy (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]) t)
  change selected V η f (1 / 2) policy t ∈ SourceSubdifferential (f t)
    (output V η f (1 / 2) policy t) at hg
  rw [hs] at hg
  exact hg

theorem a_tie (t : ℕ) (ht : 0 < t) (hx : a t = 1 / 2) : ga t = 1 := by
  have hf : lossA t = loss (1 / 2) := by simp [lossA, Nat.ne_of_gt ht]
  have hg : preferred t (fun i => lossA i.val) ∈ SourceSubdifferential (lossA t) (a t) := by
    rw [pref_A t ht, hf, hx, loss_subgradient_zero]; norm_num
  exact (selected_eq_preferred eta lossA t hg).trans (pref_A t ht)

theorem b_tie (t : ℕ) (ht : 0 < t) (hx : b t = 1 / 2) : gb t = -1 := by
  have hf : lossB t = loss (1 / 2) := by simp [lossB, Nat.ne_of_gt ht]
  have hg : preferred t (fun i => lossB i.val) ∈ SourceSubdifferential (lossB t) (b t) := by
    rw [pref_B t ht, hf, hx, loss_subgradient_zero]; norm_num
  exact (selected_eq_preferred eta lossB t hg).trans (pref_B t ht)

theorem a_below (t : ℕ) (ht : 0 < t) (hx : a t < 1 / 2) : ga t = -1 := by
  apply selected_singleton eta lossA t (lossA_on t) (-1)
  simpa only [lossA, if_neg (Nat.ne_of_gt ht)] using loss_subgradient_negative (1 / 2) (a t) hx

theorem b_above (t : ℕ) (ht : 0 < t) (hx : 1 / 2 < b t) : gb t = 1 := by
  apply selected_singleton eta lossB t (lossB_on t) 1
  simpa only [lossB, if_neg (Nat.ne_of_gt ht)] using loss_subgradient_positive (1 / 2) (b t) hx

theorem a_zero : a 0 = 1 / 2 := rfl
theorem b_zero : b 0 = 1 / 2 := rfl

theorem ga_zero : ga 0 = 0 := by
  have hg : preferred 0 (fun i => lossA i.val) ∈ SourceSubdifferential (lossA 0) (a 0) := by
    simp [preferred, lossA, flat, SourceSubdifferential]
  simpa [preferred, ga] using selected_eq_preferred eta lossA 0 hg

theorem gb_zero : gb 0 = 0 := by
  have hg : preferred 0 (fun i => lossB i.val) ∈ SourceSubdifferential (lossB 0) (b 0) := by
    simp [preferred, lossB, flat, SourceSubdifferential]
  simpa [preferred, gb] using selected_eq_preferred eta lossB 0 hg

theorem a_one : a 1 = 1 / 2 := by
  change output V eta lossA (1 / 2) policy (0 + 1) = _
  rw [output_succ]
  change BanditRL.OnlineGradientDescent.project V (a 0 - eta 0 • ga 0) = _
  rw [ga_zero, a_zero, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem b_one : b 1 = 1 / 2 := by
  change output V eta lossB (1 / 2) policy (0 + 1) = _
  rw [output_succ]
  change BanditRL.OnlineGradientDescent.project V (b 0 - eta 0 • gb 0) = _
  rw [gb_zero, b_zero, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem ga_one : ga 1 = 1 := a_tie 1 (by norm_num) a_one
theorem gb_one : gb 1 = -1 := b_tie 1 (by norm_num) b_one

theorem a_two : a 2 = 0 := by
  change output V eta lossA (1 / 2) policy (1 + 1) = _
  rw [output_succ]
  change BanditRL.OnlineGradientDescent.project V (a 1 - eta 1 • ga 1) = _
  rw [ga_one, a_one, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem b_two : b 2 = 1 := by
  change output V eta lossB (1 / 2) policy (1 + 1) = _
  rw [output_succ]
  change BanditRL.OnlineGradientDescent.project V (b 1 - eta 1 • gb 1) = _
  rw [gb_one, b_one, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem ga_two : ga 2 = -1 := a_below 2 (by norm_num) (by rw [a_two]; norm_num)
theorem gb_two : gb 2 = 1 := b_above 2 (by norm_num) (by rw [b_two]; norm_num)

theorem a_three : a 3 = 1 / 2 := by
  change output V eta lossA (1 / 2) policy (2 + 1) = _
  rw [output_succ]
  change BanditRL.OnlineGradientDescent.project V (a 2 - eta 2 • ga 2) = _
  rw [ga_two, a_two, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem b_three : b 3 = 1 / 2 := by
  change output V eta lossB (1 / 2) policy (2 + 1) = _
  rw [output_succ]
  change BanditRL.OnlineGradientDescent.project V (b 2 - eta 2 • gb 2) = _
  rw [gb_two, b_two, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem ga_three : ga 3 = 1 := a_tie 3 (by norm_num) a_three
theorem gb_three : gb 3 = -1 := b_tie 3 (by norm_num) b_three

theorem a_four : a 4 = 0 := by
  change output V eta lossA (1 / 2) policy (3 + 1) = _
  rw [output_succ]
  change BanditRL.OnlineGradientDescent.project V (a 3 - eta 3 • ga 3) = _
  rw [ga_three, a_three, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem b_four : b 4 = 1 := by
  change output V eta lossB (1 / 2) policy (3 + 1) = _
  rw [output_succ]
  change BanditRL.OnlineGradientDescent.project V (b 3 - eta 3 • gb 3) = _
  rw [gb_three, b_three, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]


theorem history_changes_actual_support :
    a 1 = b 1 ∧ lossA 1 = lossB 1 ∧ ga 1 = 1 ∧ gb 1 = -1 ∧ ga 1 ≠ gb 1 := by
  rw [a_one, b_one, ga_one, gb_one]; norm_num [lossA, lossB]

theorem legalA (T : ℕ) : LegalFeedback V eta lossA (1 / 2) policy T :=
  oracle_feedback V eta lossA (1 / 2) policy
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]) T policy_oracle
    (fun t _ => lossA_on t)

theorem legalB (T : ℕ) : LegalFeedback V eta lossB (1 / 2) policy T :=
  oracle_feedback V eta lossB (1 / 2) policy
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]) T policy_oracle
    (fun t _ => lossB_on t)

theorem a_real_regret : regret V eta lossA (1 / 2) policy (1 / 2) 4 = 1 / 2 := by
  simp only [regret, sum_range_succ, sum_range_zero, zero_add]
  change ((lossA 0 (a 0)).toReal - (lossA 0 (1 / 2)).toReal) +
    ((lossA 1 (a 1)).toReal - (lossA 1 (1 / 2)).toReal) +
    ((lossA 2 (a 2)).toReal - (lossA 2 (1 / 2)).toReal) +
    ((lossA 3 (a 3)).toReal - (lossA 3 (1 / 2)).toReal) = 1 / 2
  rw [a_zero, a_one, a_two, a_three]; norm_num [lossA, flat, loss]

theorem b_real_regret : regret V eta lossB (1 / 2) policy (1 / 2) 4 = 1 / 2 := by
  simp only [regret, sum_range_succ, sum_range_zero, zero_add]
  change ((lossB 0 (b 0)).toReal - (lossB 0 (1 / 2)).toReal) +
    ((lossB 1 (b 1)).toReal - (lossB 1 (1 / 2)).toReal) +
    ((lossB 2 (b 2)).toReal - (lossB 2 (1 / 2)).toReal) +
    ((lossB 3 (b 3)).toReal - (lossB 3 (1 / 2)).toReal) = 1 / 2
  rw [b_zero, b_one, b_two, b_three]; norm_num [lossB, flat, loss]

theorem a_energy : (∑ t ∈ range 4, ‖ga t‖ ^ 2) = (3 : ℝ) := by
  simp only [sum_range_succ, sum_range_zero, zero_add, ga_zero, ga_one, ga_two, ga_three]
  norm_num

theorem b_energy : (∑ t ∈ range 4, ‖gb t‖ ^ 2) = (3 : ℝ) := by
  simp only [sum_range_succ, sum_range_zero, zero_add, gb_zero, gb_one, gb_two, gb_three]
  norm_num

theorem a_positive_terminal : ‖a 4 - 1 / 2‖ ^ 2 / (2 * (1 / 2)) = (1 : ℝ) / 4 := by
  rw [a_four]; norm_num

theorem b_positive_terminal : ‖b 4 - 1 / 2‖ ^ 2 / (2 * (1 / 2)) = (1 : ℝ) / 4 := by
  rw [b_four]; norm_num

theorem a_exact_fixed_bound : regret V eta lossA (1 / 2) policy (1 / 2) 4 ≤
    ‖(1 / 2 : ℝ) - 1 / 2‖ ^ 2 / (2 * (1 / 2)) +
      (1 / 2 : ℝ) / 2 * (∑ t ∈ range 4, ‖ga t‖ ^ 2) -
      ‖a 4 - 1 / 2‖ ^ 2 / (2 * (1 / 2)) := by
  exact regret_fixed V (1 / 2) (by norm_num) lossA (1 / 2) policy
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]) 4
    (fun t _ => lossA_on t) (legalA 4) (1 / 2)
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval])

theorem a_fixed_rhs_equality :
    ‖(1 / 2 : ℝ) - 1 / 2‖ ^ 2 / (2 * (1 / 2)) +
      (1 / 2 : ℝ) / 2 * (∑ t ∈ range 4, ‖ga t‖ ^ 2) -
      ‖a 4 - 1 / 2‖ ^ 2 / (2 * (1 / 2)) = 1 / 2 := by
  rw [a_energy, a_positive_terminal]; norm_num

def offPathPolicy : SupportPolicy (E := ℝ) := by
  classical
  exact fun t past h f => if t = 0 ∧ h (Fin.last t) ≠ 1 / 2 then 999 else policy t past h f

theorem offPath_history_eq (η : ℕ → ℝ) (f : ℕ → ℝ → EReal) (t : ℕ) :
    history V η f (1 / 2) offPathPolicy t = history V η f (1 / 2) policy t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [history_succ, history_succ]
    have hsel : selected V η f (1 / 2) offPathPolicy t =
        selected V η f (1 / 2) policy t := by
      classical
      change offPathPolicy t (fun i => f i.val) (history V η f (1 / 2) offPathPolicy t) (f t) = _
      rw [ih]
      change (if t = 0 ∧ history V η f (1 / 2) policy t (Fin.last t) ≠ 1 / 2 then
        999 else policy t (fun i => f i.val) (history V η f (1 / 2) policy t) (f t)) = _
      by_cases ht : t = 0
      · subst t; simp [history, selected]
      · rw [if_neg (by simp [ht])]
        rfl
    have hout : output V η f (1 / 2) offPathPolicy t = output V η f (1 / 2) policy t :=
      congrArg (fun h : Fin (t + 1) → ℝ => h (Fin.last t)) ih
    rw [ih, hsel, hout]

theorem offPath_output_eq (η : ℕ → ℝ) (f : ℕ → ℝ → EReal) (t : ℕ) :
    output V η f (1 / 2) offPathPolicy t = output V η f (1 / 2) policy t := by
  exact congrArg (fun h : Fin (t + 1) → ℝ => h (Fin.last t)) (offPath_history_eq η f t)

theorem offPath_selected_eq (η : ℕ → ℝ) (f : ℕ → ℝ → EReal) (t : ℕ) :
    selected V η f (1 / 2) offPathPolicy t = selected V η f (1 / 2) policy t := by
  classical
  change offPathPolicy t (fun i => f i.val) (history V η f (1 / 2) offPathPolicy t) (f t) = _
  rw [offPath_history_eq]
  change (if t = 0 ∧ history V η f (1 / 2) policy t (Fin.last t) ≠ 1 / 2 then
    999 else policy t (fun i => f i.val) (history V η f (1 / 2) policy t) (f t)) = _
  by_cases ht : t = 0
  · subst t; simp [history, selected]
  · rw [if_neg (by simp [ht])]
    rfl

theorem offPath_legalA (η : ℕ → ℝ) (T : ℕ) :
    LegalFeedback V η lossA (1 / 2) offPathPolicy T := by
  have hg := oracle_feedback V η lossA (1 / 2) policy
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]) T policy_oracle
    (fun t _ => lossA_on t)
  intro t ht
  rw [offPath_selected_eq, offPath_output_eq]
  exact hg t ht

theorem offPath_not_oracle : ¬ OracleLaw V offPathPolicy := by
  intro hp
  have hg := hp 0 (fun i => Fin.elim0 i) (fun _ => (3 / 4 : ℝ)) (flat 0) (flat_on 0)
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval])
  have h999 : (999 : ℝ) ∈ SourceSubdifferential (flat 0) (3 / 4) := by
    norm_num [offPathPolicy] at hg
    exact hg
  have htest := h999 (1 : ℝ)
  norm_num [flat] at htest
  change (1 / 4 : ℝ) * 999 ≤ 0 at htest
  norm_num at htest

theorem offPath_actual_fixed : regret V eta lossA (1 / 2) offPathPolicy (1 / 2) 4 ≤
    ‖(1 / 2 : ℝ) - 1 / 2‖ ^ 2 / (2 * (1 / 2)) +
      (1 / 2 : ℝ) / 2 * (∑ t ∈ range 4,
        ‖selected V eta lossA (1 / 2) offPathPolicy t‖ ^ 2) -
      ‖output V eta lossA (1 / 2) offPathPolicy 4 - 1 / 2‖ ^ 2 / (2 * (1 / 2)) := by
  exact regret_fixed V (1 / 2) (by norm_num) lossA (1 / 2) offPathPolicy
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]) 4
    (fun t _ => lossA_on t) (offPath_legalA eta 4) (1 / 2)
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval])


theorem norm_bound_A (η : ℕ → ℝ) (t : ℕ) :
    ‖selected V η lossA (1 / 2) policy t‖ ≤ 1 := by
  by_cases ht : t = 0
  · subst t
    have hg : preferred 0 (fun i => lossA i.val) ∈ SourceSubdifferential (lossA 0)
        (output V η lossA (1 / 2) policy 0) := by
      simp [preferred, lossA, flat, SourceSubdifferential]
    have hzero : selected V η lossA (1 / 2) policy 0 = 0 := by
      simpa [preferred] using selected_eq_preferred η lossA 0 hg
    rw [hzero]; norm_num
  · have hg := policy_oracle t (fun i => lossA i.val) (history V η lossA (1 / 2) policy t)
      (lossA t) (lossA_on t)
      (output_mem V η lossA (1 / 2) policy
        (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]) t)
    apply loss_subgradient_bound (1 / 2) (output V η lossA (1 / 2) policy t)
      (selected V η lossA (1 / 2) policy t)
    change selected V η lossA (1 / 2) policy t ∈ SourceSubdifferential (lossA t)
      (output V η lossA (1 / 2) policy t) at hg
    simpa only [lossA, if_neg ht] using hg

theorem unit_diameter : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ (1 : ℝ) := by
  intro x hx y hy
  change 0 ≤ x ∧ x ≤ 1 at hx
  change 0 ≤ y ∧ y ≤ 1 at hy
  change |x - y| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem offPath_tuned_all_comparators : ∀ u ∈ V.carrier,
    regret V eta lossA (1 / 2) offPathPolicy u 4 ≤ 2 := by
  have hb := regret_tuned V lossA (1 / 2) offPathPolicy
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]) 4 (by norm_num)
    1 1 (by norm_num) (by norm_num) (fun t _ => lossA_on t)
    (offPath_legalA _ 4) unit_diameter
    (fun t _ => by rw [offPath_selected_eq]; exact norm_bound_A _ t)
  norm_num at hb
  simpa only [eta] using hb

def harmonic (t : ℕ) : ℝ := (1 / 2) / ((t : ℝ) + 1)
abbrev ah (t : ℕ) : ℝ := output V harmonic lossA (1 / 2) policy t
abbrev gh (t : ℕ) : ℝ := selected V harmonic lossA (1 / 2) policy t

theorem ah_zero : ah 0 = 1 / 2 := rfl

theorem gh_zero : gh 0 = 0 := by
  have hg : preferred 0 (fun i => lossA i.val) ∈ SourceSubdifferential (lossA 0) (ah 0) := by
    simp [preferred, lossA, flat, SourceSubdifferential]
  simpa [gh, preferred] using selected_eq_preferred harmonic lossA 0 hg

theorem ah_one : ah 1 = 1 / 2 := by
  change output V harmonic lossA (1 / 2) policy (0 + 1) = _
  rw [output_succ]
  change BanditRL.OnlineGradientDescent.project V (ah 0 - harmonic 0 • gh 0) = _
  rw [gh_zero, ah_zero, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [harmonic]

theorem gh_one : gh 1 = 1 := by
  have hg : preferred 1 (fun i => lossA i.val) ∈ SourceSubdifferential (lossA 1) (ah 1) := by
    rw [pref_A 1 (by norm_num), ah_one]
    change (1 : ℝ) ∈ SourceSubdifferential (loss (1 / 2)) (1 / 2)
    rw [loss_subgradient_zero]; norm_num
  simpa only [gh, pref_A 1 (by norm_num)] using selected_eq_preferred harmonic lossA 1 hg

theorem ah_two : ah 2 = 1 / 4 := by
  change output V harmonic lossA (1 / 2) policy (1 + 1) = _
  rw [output_succ]
  change BanditRL.OnlineGradientDescent.project V (ah 1 - harmonic 1 • gh 1) = _
  rw [gh_one, ah_one, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [harmonic]

theorem gh_two : gh 2 = -1 := by
  apply selected_singleton harmonic lossA 2 (lossA_on 2) (-1)
  change SourceSubdifferential (loss (1 / 2)) (ah 2) = {(-1 : ℝ)}
  exact loss_subgradient_negative (1 / 2) (ah 2) (by rw [ah_two]; norm_num)

theorem ah_three : ah 3 = 5 / 12 := by
  change output V harmonic lossA (1 / 2) policy (2 + 1) = _
  rw [output_succ]
  change BanditRL.OnlineGradientDescent.project V (ah 2 - harmonic 2 • gh 2) = _
  rw [gh_two, ah_two, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [harmonic]

theorem gh_three : gh 3 = -1 := by
  apply selected_singleton harmonic lossA 3 (lossA_on 3) (-1)
  change SourceSubdifferential (loss (1 / 2)) (ah 3) = {(-1 : ℝ)}
  exact loss_subgradient_negative (1 / 2) (ah 3) (by rw [ah_three]; norm_num)

theorem ah_four : ah 4 = 13 / 24 := by
  change output V harmonic lossA (1 / 2) policy (3 + 1) = _
  rw [output_succ]
  change BanditRL.OnlineGradientDescent.project V (ah 3 - harmonic 3 • gh 3) = _
  rw [gh_three, ah_three, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [harmonic]

theorem harmonic_energy : (∑ t ∈ range 4, harmonic t / 2 * ‖gh t‖ ^ 2) = (13 : ℝ) / 48 := by
  simp only [sum_range_succ, sum_range_zero, zero_add, gh_zero, gh_one, gh_two, gh_three]
  norm_num [harmonic]

theorem harmonic_last_eta_and_positive_terminal :
    harmonic (4 - 1) = 1 / 8 ∧ ‖ah 4 - 1 / 2‖ ^ 2 / (2 * harmonic (4 - 1)) = (1 : ℝ) / 144 := by
  rw [ah_four]; norm_num [harmonic]

theorem harmonic_real_regret : regret V harmonic lossA (1 / 2) policy (1 / 2) 4 = 1 / 3 := by
  simp only [regret, sum_range_succ, sum_range_zero, zero_add]
  change ((lossA 0 (ah 0)).toReal - (lossA 0 (1 / 2)).toReal) +
    ((lossA 1 (ah 1)).toReal - (lossA 1 (1 / 2)).toReal) +
    ((lossA 2 (ah 2)).toReal - (lossA 2 (1 / 2)).toReal) +
    ((lossA 3 (ah 3)).toReal - (lossA 3 (1 / 2)).toReal) = 1 / 3
  rw [ah_zero, ah_one, ah_two, ah_three]; norm_num [lossA, flat, loss]

theorem harmonic_actual_variable : regret V harmonic lossA (1 / 2) policy (1 / 2) 4 ≤
    (1 : ℝ) ^ 2 / (2 * harmonic (4 - 1)) +
      (∑ t ∈ range 4, harmonic t / 2 * ‖gh t‖ ^ 2) -
      ‖ah 4 - 1 / 2‖ ^ 2 / (2 * harmonic (4 - 1)) := by
  apply regret_variable_bound V harmonic lossA (1 / 2) policy
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]) 4 (by norm_num)
    (fun t ht => by interval_cases t <;> norm_num [harmonic])
    (fun t ht => by
      have hb : t < 3 := by omega
      interval_cases t <;> norm_num [harmonic])
    (fun t _ => lossA_on t)
    (oracle_feedback V harmonic lossA (1 / 2) policy
      (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]) 4 policy_oracle
      (fun t _ => lossA_on t)) 1 unit_diameter (1 / 2)
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval])

def futureLoss (t : ℕ) : ℝ → EReal := if t < 4 then lossA t else fun _ => ⊥
def futureEta (t : ℕ) : ℝ := if t < 4 then eta t else -99

theorem invalid_future_causal : output V futureEta futureLoss (1 / 2) policy 4 = a 4 := by
  apply output_prefix V futureEta eta futureLoss lossA (1 / 2) policy 4
  · intro s hs; simp [futureEta, hs]
  · intro s hs; simp [futureLoss, hs]

theorem invalid_future_current_loss : futureLoss 4 0 = ⊥ ∧ futureEta 4 = -99 := by
  norm_num [futureLoss, futureEta]

theorem zero_horizon : regret V futureEta futureLoss (1 / 2) offPathPolicy (1 / 2) 0 = 0 := by
  simp [regret]

theorem canonical_invalid_future_bridge (t : ℕ) :
    output V futureEta futureLoss (1 / 2) canonicalPolicy t =
      BanditRL.OnlineSubgradientDescent.iterate V futureEta futureLoss (1 / 2) t :=
  canonical_output V futureEta futureLoss (1 / 2) t

/-- An invalid loss whose support set at zero is actually empty. -/
def emptySupportLoss (x : ℝ) : EReal := if x = 0 then 1 else 0

theorem empty_support_at_zero : SourceSubdifferential emptySupportLoss 0 = ∅ := by
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hg
  have hp := hg (1 : ℝ)
  have hm := hg (-1 : ℝ)
  norm_num [emptySupportLoss] at hp hm
  change (1 : ℝ) + (1 : ℝ) * g ≤ 0 at hp
  change (1 : ℝ) + (-1 : ℝ) * g ≤ 0 at hm
  linarith

theorem empty_support_current_fallback :
    BanditRL.OnlineSubgradientDescent.currentSubgradient emptySupportLoss 0 = 0 := by
  unfold BanditRL.OnlineSubgradientDescent.currentSubgradient
  rw [empty_support_at_zero]
  simp

theorem empty_support_actual_selected :
    selected V eta (fun _ => emptySupportLoss) 0 canonicalPolicy 0 = 0 := by
  rw [canonical_selected]
  exact empty_support_current_fallback

theorem empty_support_actual_output :
    output V eta (fun _ => emptySupportLoss) 0 canonicalPolicy 1 = 0 := by
  rw [output_succ, output_zero, empty_support_actual_selected,
    V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num

theorem empty_support_not_legal :
    ¬ LegalFeedback V eta (fun _ => emptySupportLoss) 0 canonicalPolicy 1 := by
  intro h
  have hg := h 0 (by norm_num)
  rw [output_zero, empty_support_at_zero] at hg
  exact hg

/-- The fixed performance theorem at T=0 cancels a nonzero endpoint distance. -/
theorem zero_horizon_actual_fixed :
    regret V eta futureLoss (1 / 2) offPathPolicy (1 / 3) 0 ≤
      ‖(1 / 2 : ℝ) - 1 / 3‖ ^ 2 / (2 * (1 / 2)) +
        (1 / 2 : ℝ) / 2 * (∑ t ∈ range 0,
          ‖selected V eta futureLoss (1 / 2) offPathPolicy t‖ ^ 2) -
        ‖output V eta futureLoss (1 / 2) offPathPolicy 0 - 1 / 3‖ ^ 2 /
          (2 * (1 / 2)) := by
  exact regret_fixed V (1 / 2) (by norm_num) futureLoss (1 / 2) offPathPolicy
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]) 0
    (fun t ht => by omega) (fun t ht => by omega) (1 / 3)
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval])

theorem zero_horizon_positive_cancelling_endpoints :
    ‖(1 / 2 : ℝ) - 1 / 3‖ ^ 2 / (2 * (1 / 2)) = (1 : ℝ) / 36 ∧
    ‖output V eta futureLoss (1 / 2) offPathPolicy 0 - 1 / 3‖ ^ 2 /
      (2 * (1 / 2)) = (1 : ℝ) / 36 := by
  rw [output_zero]
  norm_num

end OSDPolicyProbe
