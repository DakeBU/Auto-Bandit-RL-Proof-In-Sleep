import BanditRLProof.Algorithms.MOSSHistory

open BanditRLProof MeasureTheory

example {k : ℕ} (hk : 0 < k) (n t : ℕ) :
    Measurable (MOSS.historyAction hk n t) :=
  MOSS.measurable_historyAction hk n t

example {k : ℕ} (hk : 0 < k) (n t : ℕ)
    (history : History.FinitePairHistory (Fin k) ℝ t) :
    (MOSS.historyAlgorithm hk n).policy t history =
      Measure.dirac (MOSS.historyAction hk n t history) :=
  MOSS.historyAlgorithm_policy_apply hk n t history

example (empirical : Fin 3 → ℝ) (pulls : Fin 3 → ℕ) :
    MOSS.action (by decide : 0 < 3) 100 1 empirical pulls = 1 := by
  exact MOSS.action_of_lt (by decide) 100 1 empirical pulls (by decide)

example {k : ℕ} (hk : 0 < k) (n t : ℕ)
    (mean empirical : Fin k → ℝ) (pulls : Fin k → ℕ)
    (best chosen : Fin k) (deficit : ℝ) (ht : k ≤ t)
    (hselect : MOSS.action hk n t empirical pulls = chosen)
    (hbest : mean best - deficit ≤ MOSS.index n empirical pulls best)
    (hgap : 2 * deficit < mean best - mean chosen) :
    mean chosen + (mean best - mean chosen) / 2 < MOSS.index n empirical pulls chosen :=
  MOSS.selected_index_gt_mean_add_half_gap hk n t mean empirical pulls
    best chosen deficit ht hselect hbest hgap

#print axioms MOSS.radius_sq
#print axioms MOSS.selected_index_gt_mean_add_half_gap
#print axioms MOSS.measurable_historyAction
#print axioms MOSS.historyAlgorithm
