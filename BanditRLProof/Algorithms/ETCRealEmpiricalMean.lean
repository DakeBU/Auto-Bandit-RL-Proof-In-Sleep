import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasurableLocalQuantities
import BanditRLProof.Algorithms.ETCExpectedPullCount

/-!
# Native Real ETC empirical means and finite argmax

This module supplies the Real-valued empirical-mean and measurable finite
argmax surface needed before transporting ETC to an arbitrary native Real
environment. It stays below reward-law identification, concentration, and the
final `IsAlgEnvSeq` regret theorem.
-/

universe u

open MeasureTheory

namespace BanditRLProof
namespace ETC

/-- The exploration empirical mean formed directly from a Real reward trace. -/
noncomputable def realEmpMeanAtExploration {K : Nat} (spec : ETC.Spec K)
    (baseCommitArm : Fin K) (reward : RewardTrace Real) (a : Fin K) : Real :=
  sumRewards (ETC.actionWithCommit spec baseCommitArm) reward a
      (spec.explorationPulls * K) /
    (pullCount (ETC.actionWithCommit spec baseCommitArm) a
      (spec.explorationPulls * K) : Real)

/-- The deterministic exploration count removes the pull-count denominator. -/
theorem realEmpMeanAtExploration_eq_sumRewards_div_explorationPulls
    {K : Nat} (spec : ETC.Spec K) (baseCommitArm : Fin K)
    (reward : RewardTrace Real) (a : Fin K) :
    ETC.realEmpMeanAtExploration spec baseCommitArm reward a =
      sumRewards (ETC.actionWithCommit spec baseCommitArm) reward a
          (spec.explorationPulls * K) /
        (spec.explorationPulls : Real) := by
  simp [ETC.realEmpMeanAtExploration,
    ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq]

/-- Real exploration empirical means are measurable from measurable rewards. -/
theorem measurable_realEmpMeanAtExploration
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (spec : ETC.Spec K) (baseCommitArm a : Fin K)
    (reward : Omega -> RewardTrace Real)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      ETC.realEmpMeanAtExploration spec baseCommitArm (reward omega) a) := by
  have hsum : Measurable (fun omega : Omega =>
      sumRewards (ETC.actionWithCommit spec baseCommitArm) (reward omega) a
        (spec.explorationPulls * K)) := by
    simpa using
      (measurable_sumRewards
        (action := fun _ : Omega => ETC.actionWithCommit spec baseCommitArm)
        (reward := reward)
        (fun _t => measurable_const) hreward a
        (spec.explorationPulls * K))
  simpa [ETC.realEmpMeanAtExploration] using
    hsum.div_const
      (pullCount (ETC.actionWithCommit spec baseCommitArm) a
        (spec.explorationPulls * K) : Real)

private theorem real_score_le_foldl_select
    {K : Nat} (scores : Fin K -> Real) (init : Fin K) :
    forall l : List (Fin K),
      (forall a : Fin K, List.Mem a l ->
        scores a <=
          scores
            (l.foldl
              (fun best arm : Fin K =>
                if scores best < scores arm then arm else best)
              init)) /\
      scores init <=
        scores
          (l.foldl
            (fun best arm : Fin K =>
              if scores best < scores arm then arm else best)
            init)
  | [] => by
      exact And.intro (by intro _ ha; cases ha) (by simp)
  | arm :: rest => by
      let select := fun best arm : Fin K =>
        if scores best < scores arm then arm else best
      let next := select init arm
      have ih := real_score_le_foldl_select (scores := scores) next rest
      have harm_next : scores arm <= scores next := by
        exact if hlt : scores init < scores arm then
          by simp [next, select, hlt]
        else
          by simp [next, select, hlt, le_of_not_gt hlt]
      exact And.intro
        (by
          intro a ha
          cases ha with
          | head => exact le_trans harm_next ih.2
          | tail _ ha => exact ih.1 a ha)
        (by
          have hinit_next : scores init <= scores next := by
            exact if hlt : scores init < scores arm then
              by simpa [next, select, hlt] using le_of_lt hlt
            else
              by simp [next, select, hlt]
          exact le_trans hinit_next ih.2)

/-- A deterministic finite argmax for Real-valued arm scores. -/
noncomputable def realArgmaxCommit {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) : Fin K :=
  (List.finRange K).foldl
    (fun best arm : Fin K =>
      if scores best < scores arm then arm else best)
    (Fin.mk 0 hK)

/-- The Real finite argmax dominates every arm score. -/
theorem realArgmaxCommit_spec {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) (a : Fin K) :
    scores a <= scores (ETC.realArgmaxCommit hK scores) := by
  exact
    (real_score_le_foldl_select
      (scores := scores) (init := Fin.mk 0 hK) (List.finRange K)).1
      a (List.mem_finRange a)

/-- On a constant score vector, the tie rule keeps the initial arm `0`. -/
@[simp] theorem realArgmaxCommit_const {K : Nat} (hK : 0 < K) (c : Real) :
    ETC.realArgmaxCommit hK (fun _a : Fin K => c) = Fin.mk 0 hK := by
  simp [ETC.realArgmaxCommit]

private theorem measurable_selected_real_score
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (scores : Omega -> Fin K -> Real)
    (hscores : forall a : Fin K,
      Measurable (fun omega : Omega => scores omega a))
    (best : Omega -> Fin K) (hbest : Measurable best) :
    Measurable (fun omega : Omega => scores omega (best omega)) := by
  classical
  have hsum : Measurable (fun omega : Omega =>
      (Finset.univ : Finset (Fin K)).sum (fun a =>
        if best omega = a then scores omega a else 0)) := by
    refine Finset.measurable_sum _ ?_
    intro a _ha
    exact Measurable.ite
      (measurableSet_eq_fun hbest measurable_const)
      (hscores a) measurable_const
  convert hsum using 1
  funext omega
  simp

private theorem measurable_foldl_real_select
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (scores : Omega -> Fin K -> Real)
    (hscores : forall a : Fin K,
      Measurable (fun omega : Omega => scores omega a))
    (best : Omega -> Fin K) (hbest : Measurable best) :
    forall l : List (Fin K),
      Measurable (fun omega : Omega =>
        l.foldl
          (fun best arm : Fin K =>
            if scores omega best < scores omega arm then arm else best)
          (best omega))
  | [] => by simpa using hbest
  | arm :: rest => by
      have hselected : Measurable (fun omega : Omega =>
          scores omega (best omega)) :=
        measurable_selected_real_score scores hscores best hbest
      have hnext : Measurable (fun omega : Omega =>
          if scores omega (best omega) < scores omega arm then
            arm
          else
            best omega) :=
        Measurable.ite
          (measurableSet_lt hselected (hscores arm))
          measurable_const hbest
      simpa using
        (measurable_foldl_real_select scores hscores
          (fun omega : Omega =>
            if scores omega (best omega) < scores omega arm then
              arm
            else
              best omega)
          hnext rest)

/-- The finite Real argmax is measurable when every score coordinate is. -/
theorem measurable_realArgmaxCommit_of_forall_measurable
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K) (scores : Omega -> Fin K -> Real)
    (hscores : forall a : Fin K,
      Measurable (fun omega : Omega => scores omega a)) :
    Measurable (fun omega : Omega => ETC.realArgmaxCommit hK (scores omega)) := by
  unfold ETC.realArgmaxCommit
  exact measurable_foldl_real_select scores hscores
    (fun _omega : Omega => Fin.mk 0 hK) measurable_const (List.finRange K)

/-- Commit to the arm maximizing the native Real exploration means. -/
noncomputable def realExplorationArgmaxCommit
    {K : Nat} (spec : ETC.Spec K) (baseCommitArm : Fin K)
    (reward : RewardTrace Real) : Fin K :=
  ETC.realArgmaxCommit spec.hK
    (fun a => ETC.realEmpMeanAtExploration spec baseCommitArm reward a)

/-- Native Real ETC trace: round-robin exploration, then Real empirical argmax. -/
noncomputable def realExplorationArgmaxAction
    {K : Nat} (spec : ETC.Spec K) (baseCommitArm : Fin K)
    (reward : RewardTrace Real) : ActionTrace (Fin K) :=
  ETC.actionWithCommit spec
    (ETC.realExplorationArgmaxCommit spec baseCommitArm reward)

/-- The reward-dependent native Real ETC commit arm is measurable. -/
theorem measurable_realExplorationArgmaxCommit
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (spec : ETC.Spec K) (baseCommitArm : Fin K)
    (reward : Omega -> RewardTrace Real)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      ETC.realExplorationArgmaxCommit spec baseCommitArm (reward omega)) := by
  apply ETC.measurable_realArgmaxCommit_of_forall_measurable
  intro a
  exact ETC.measurable_realEmpMeanAtExploration
    spec baseCommitArm a reward hreward

/-- Exact expected pull count for the native Real empirical-argmax ETC trace. -/
theorem integral_real_pullCount_realExplorationArgmaxAction_eq_exploration_add_remaining_mul_commit_prob
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (baseCommitArm : Fin K)
    (reward : Omega -> RewardTrace Real)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (a : Fin K) (n : Nat)
    (hn : K * spec.explorationPulls <= n) :
    integral mu (fun omega : Omega =>
      ((pullCount
        (ETC.realExplorationArgmaxAction spec baseCommitArm (reward omega))
        a n : Nat) : Real)) =
      (spec.explorationPulls : Real) +
        ((n - K * spec.explorationPulls : Nat) : Real) *
          mu.real {omega : Omega |
            ETC.realExplorationArgmaxCommit spec baseCommitArm
              (reward omega) = a} := by
  exact
    ETC.integral_real_pullCount_actionWithCommit_choice_eq_exploration_add_remaining_mul_commit_prob
      mu spec
      (fun omega : Omega =>
        ETC.realExplorationArgmaxCommit spec baseCommitArm (reward omega))
      a n hn
      (ETC.measurable_realExplorationArgmaxCommit
        spec baseCommitArm reward hreward)

/-- A commit-fiber bound immediately yields the native Real expected count bound. -/
theorem integral_real_pullCount_realExplorationArgmaxAction_le_exploration_add_remaining_mul_of_commit_prob_le
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (baseCommitArm : Fin K)
    (reward : Omega -> RewardTrace Real)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (a : Fin K) (n : Nat) (p : Real)
    (hn : K * spec.explorationPulls <= n)
    (hprob : mu.real {omega : Omega |
      ETC.realExplorationArgmaxCommit spec baseCommitArm (reward omega) = a}
        <= p) :
    integral mu (fun omega : Omega =>
      ((pullCount
        (ETC.realExplorationArgmaxAction spec baseCommitArm (reward omega))
        a n : Nat) : Real)) <=
      (spec.explorationPulls : Real) +
        ((n - K * spec.explorationPulls : Nat) : Real) * p := by
  exact
    ETC.integral_real_pullCount_actionWithCommit_choice_le_exploration_add_remaining_mul_of_commit_prob_le
      mu spec
      (fun omega : Omega =>
        ETC.realExplorationArgmaxCommit spec baseCommitArm (reward omega))
      a n p hn
      (ETC.measurable_realExplorationArgmaxCommit
        spec baseCommitArm reward hreward)
      hprob

end ETC
end BanditRLProof
