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
  simpa [preferred] using selected_eq_preferred eta lossA 0 hg

theorem gb_zero : gb 0 = 0 := by
  have hg : preferred 0 (fun i => lossB i.val) ∈ SourceSubdifferential (lossB 0) (b 0) := by
    simp [preferred, lossB, flat, SourceSubdifferential]
  simpa [preferred] using selected_eq_preferred eta lossB 0 hg

theorem a_one : a 1 = 1 / 2 := by
  change output V eta lossA (1 / 2) policy (0 + 1) = _
  rw [output_succ, ga_zero, a_zero, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem b_one : b 1 = 1 / 2 := by
  change output V eta lossB (1 / 2) policy (0 + 1) = _
  rw [output_succ, gb_zero, b_zero, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem ga_one : ga 1 = 1 := a_tie 1 (by norm_num) a_one
theorem gb_one : gb 1 = -1 := b_tie 1 (by norm_num) b_one

theorem a_two : a 2 = 0 := by
  change output V eta lossA (1 / 2) policy (1 + 1) = _
  rw [output_succ, ga_one, a_one, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem b_two : b 2 = 1 := by
  change output V eta lossB (1 / 2) policy (1 + 1) = _
  rw [output_succ, gb_one, b_one, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem ga_two : ga 2 = -1 := a_below 2 (by norm_num) (by rw [a_two]; norm_num)
theorem gb_two : gb 2 = 1 := b_above 2 (by norm_num) (by rw [b_two]; norm_num)

theorem a_three : a 3 = 1 / 2 := by
  change output V eta lossA (1 / 2) policy (2 + 1) = _
  rw [output_succ, ga_two, a_two, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem b_three : b 3 = 1 / 2 := by
  change output V eta lossB (1 / 2) policy (2 + 1) = _
  rw [output_succ, gb_two, b_two, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem ga_three : ga 3 = 1 := a_tie 3 (by norm_num) a_three
theorem gb_three : gb 3 = -1 := b_tie 3 (by norm_num) b_three

theorem a_four : a 4 = 0 := by
  change output V eta lossA (1 / 2) policy (3 + 1) = _
  rw [output_succ, ga_three, a_three, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

theorem b_four : b 4 = 1 := by
  change output V eta lossB (1 / 2) policy (3 + 1) = _
  rw [output_succ, gb_three, b_three, V, BanditRL.OnlineGradientDescent.project_unitInterval]
  norm_num [eta]

end OSDPolicyProbe
