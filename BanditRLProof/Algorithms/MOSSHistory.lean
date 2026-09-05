import BanditRLProof.Algorithms.MOSS
import BanditRLProof.Algorithms.UCBRealHistoryIndex
import BanditRLProof.Algorithms.ThompsonAlgorithmDensityProcess

/-!
# MOSS on the common finite-history policy interface

An inclusive history at t contains t+1 observations; the successor selector
therefore calls the source action at t+1. No reward law or concentration
certificate is required to construct this deterministic Markov policy.
-/

namespace BanditRLProof.MOSS

open MeasureTheory ProbabilityTheory

/-- Source MOSS action after an inclusive finite action/reward history. -/
noncomputable def historyAction {k : ℕ} (hk : 0 < k) (n t : ℕ)
    (history : History.FinitePairHistory (Fin k) ℝ t) : Fin k :=
  action hk n (t + 1) (ETC.realHistoryEmpMean t history)
    (ETC.realHistoryPullCount t history)

theorem measurable_historyAction {k : ℕ} (hk : 0 < k) (n t : ℕ) :
    Measurable (historyAction hk n t) := by
  unfold historyAction action
  split_ifs with ht
  · exact measurable_const
  · change Measurable (fun history : History.FinitePairHistory (Fin k) ℝ t =>
      ETC.realArgmaxCommit hk (index n (ETC.realHistoryEmpMean t history)
        (ETC.realHistoryPullCount t history)))
    apply ETC.measurable_realArgmaxCommit_of_forall_measurable
    intro a
    exact (UCB.measurable_realHistoryEmpMean t a).add
      ((measurable_of_countable (radius n k)).comp
        (UCB.measurable_realHistoryPullCount t a))

/-- Concrete MOSS policy on the history interface shared by Chapter 13's
minimax regret functional. Initial action is arm zero. -/
noncomputable def historyAlgorithm {k : ℕ} (hk : 0 < k) (n : ℕ) :
    Thompson.HistoryAlgorithm (Fin k) ℝ where
  policy t := Kernel.deterministic (historyAction hk n t)
    (measurable_historyAction hk n t)
  initialAction := Measure.dirac ⟨0, hk⟩

@[simp] theorem historyAlgorithm_policy_apply {k : ℕ} (hk : 0 < k)
    (n t : ℕ) (history : History.FinitePairHistory (Fin k) ℝ t) :
    (historyAlgorithm hk n).policy t history =
      Measure.dirac (historyAction hk n t history) := by
  rw [historyAlgorithm, Kernel.deterministic_apply]

/-- Subsequent initialization rounds select the corresponding arm. -/
theorem historyAction_initialization {k : ℕ} (hk : 0 < k) (n t : ℕ)
    (history : History.FinitePairHistory (Fin k) ℝ t) (ht : t + 1 < k) :
    historyAction hk n t history = ⟨t + 1, ht⟩ :=
  action_of_lt hk n (t + 1) _ _ ht

/-- Exact post-initialization source index maximality on visible history. -/
theorem historyAction_index_max {k : ℕ} (hk : 0 < k) (n t : ℕ)
    (history : History.FinitePairHistory (Fin k) ℝ t) (ht : k ≤ t + 1)
    (a : Fin k) :
    index n (ETC.realHistoryEmpMean t history) (ETC.realHistoryPullCount t history) a ≤
      index n (ETC.realHistoryEmpMean t history) (ETC.realHistoryPullCount t history)
        (historyAction hk n t history) :=
  action_index_max hk n (t + 1) _ _ ht a

end BanditRLProof.MOSS
