import BanditRLProof.Algorithms.UCB
import BanditRLProof.Algorithms.ETCRealHistoryScore
import BanditRLProof.MeasurableLocalQuantities
import BanditRLProof.MeasurablePullCountCast

/-!
# Native Real UCB history index

This module mirrors the path-dependent score used by the pinned LML UCB
route.  In particular, the confidence width divides by the realized pull
count.  It is therefore distinct from the earlier UCB surface whose proxy is
deterministic in the sample point.
-/

namespace BanditRLProof
namespace UCB

/-- Real empirical mean of one arm before time `n`. -/
noncomputable def realEmpiricalMean
    {K : Nat} (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (arm : Fin K) (n : Nat) : Real :=
  sumRewards action reward arm n / (pullCount action arm n : Real)

/-- LML-shaped path-dependent UCB width before time `n`. -/
noncomputable def realWidth
    {K : Nat} (action : ActionTrace (Fin K)) (c : Real)
    (arm : Fin K) (n : Nat) : Real :=
  Real.sqrt
    (2 * c * Real.log ((n + 1 : Nat) : Real) /
      (pullCount action arm n : Real))

/-- Real empirical mean plus the realized pull-count confidence width. -/
noncomputable def realIndex
    {K : Nat} (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (c : Real) (arm : Fin K) (n : Nat) : Real :=
  realEmpiricalMean action reward arm n + realWidth action c arm n

/-- Inclusive finite-history version of the LML UCB width. -/
noncomputable def realHistoryWidth
    {K : Nat} (c : Real) (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (arm : Fin K) : Real :=
  Real.sqrt
    (2 * c * Real.log ((n + 2 : Nat) : Real) /
      (ETC.realHistoryPullCount n history arm : Real))

/-- Inclusive finite-history Real UCB score. -/
noncomputable def realHistoryIndex
    {K : Nat} (c : Real) (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (arm : Fin K) : Real :=
  ETC.realHistoryEmpMean n history arm +
    realHistoryWidth c n history arm

/-- Least-encoded maximizer of the path-dependent Real UCB index. -/
noncomputable def realIndexAction
    {K : Nat} (hK : 0 < K)
    (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (c : Real) (n : Nat) : Fin K :=
  ETC.realLeastEncodedArgmax hK
    (fun arm => realIndex action reward c arm n)

/-- Least-encoded maximizer on an inclusive finite pair history. -/
noncomputable def realHistoryIndexAction
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) : Fin K :=
  ETC.realLeastEncodedArgmax hK
    (fun arm => realHistoryIndex c n history arm)

/-- The trace empirical mean is measurable under timewise measurable data. -/
theorem measurable_realEmpiricalMean
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    [MeasurableSingletonClass (Fin K)]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (haction : forall t, Measurable (fun omega => action omega t))
    (hreward : forall t, Measurable (fun omega => reward omega t))
    (arm : Fin K) (n : Nat) :
    Measurable (fun omega => realEmpiricalMean (action omega) (reward omega) arm n) := by
  exact
    (measurable_sumRewards action reward haction hreward arm n).div
      (measurable_natCast_pullCount
        (Beta := Real) action haction arm n)

/-- The realized pull-count UCB width is measurable. -/
theorem measurable_realWidth
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    [MeasurableSingletonClass (Fin K)]
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t, Measurable (fun omega => action omega t))
    (c : Real) (arm : Fin K) (n : Nat) :
    Measurable (fun omega => realWidth (action omega) c arm n) := by
  exact
    (measurable_const.div
      (measurable_natCast_pullCount
        (Beta := Real) action haction arm n)).sqrt

/-- Every coordinate of the realized UCB index is measurable. -/
theorem measurable_realIndex
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    [MeasurableSingletonClass (Fin K)]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (haction : forall t, Measurable (fun omega => action omega t))
    (hreward : forall t, Measurable (fun omega => reward omega t))
    (c : Real) (arm : Fin K) (n : Nat) :
    Measurable (fun omega => realIndex (action omega) (reward omega) c arm n) := by
  exact
    (measurable_realEmpiricalMean action reward haction hreward arm n).add
      (measurable_realWidth action haction c arm n)

/-- The least-encoded realized UCB index action maximizes every arm score. -/
theorem realIndexAction_spec
    {K : Nat} (hK : 0 < K)
    (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (c : Real) (n : Nat) (arm : Fin K) :
    realIndex action reward c arm n <=
      realIndex action reward c (realIndexAction hK action reward c n) n := by
  exact
    ETC.realLeastEncodedArgmax_spec hK
      (fun candidate => realIndex action reward c candidate n) arm

/-- The least-encoded realized UCB index action is measurable. -/
theorem measurable_realIndexAction
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    [MeasurableSingletonClass (Fin K)]
    (hK : 0 < K)
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (haction : forall t, Measurable (fun omega => action omega t))
    (hreward : forall t, Measurable (fun omega => reward omega t))
    (c : Real) (n : Nat) :
    Measurable (fun omega => realIndexAction hK (action omega) (reward omega) c n) := by
  simp only [realIndexAction, ETC.realLeastEncodedArgmax_eq_realArgmaxCommit]
  apply ETC.measurable_realArgmaxCommit_of_forall_measurable
  intro arm
  exact measurable_realIndex action reward haction hreward c arm n

/-- Inclusive finite-history empirical means agree with the trace prefix. -/
theorem realHistoryEmpiricalMean_finitePairHistoryOfTrace
    {K : Nat} (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (n : Nat) (arm : Fin K) :
    ETC.realHistoryEmpMean n
        (History.finitePairHistoryOfTrace action reward n) arm =
      realEmpiricalMean action reward arm (n + 1) := by
  exact ETC.realHistoryEmpMean_finitePairHistoryOfTrace action reward n arm

/-- Inclusive finite-history widths agree with the trace width at `n + 1`. -/
theorem realHistoryWidth_finitePairHistoryOfTrace
    {K : Nat} (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (c : Real) (n : Nat) (arm : Fin K) :
    realHistoryWidth c n
        (History.finitePairHistoryOfTrace action reward n) arm =
      realWidth action c arm (n + 1) := by
  simp [realHistoryWidth, realWidth,
    ETC.realHistoryPullCount_finitePairHistoryOfTrace, Nat.add_assoc]

/-- Inclusive finite-history UCB scores agree with the trace score. -/
theorem realHistoryIndex_finitePairHistoryOfTrace
    {K : Nat} (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (c : Real) (n : Nat) (arm : Fin K) :
    realHistoryIndex c n
        (History.finitePairHistoryOfTrace action reward n) arm =
      realIndex action reward c arm (n + 1) := by
  rw [realHistoryIndex, realIndex,
    realHistoryEmpiricalMean_finitePairHistoryOfTrace,
    realHistoryWidth_finitePairHistoryOfTrace]

/-- The least-encoded history selector is exactly the trace selector. -/
theorem realHistoryIndexAction_finitePairHistoryOfTrace
    {K : Nat} (hK : 0 < K)
    (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (c : Real) (n : Nat) :
    realHistoryIndexAction hK c n
        (History.finitePairHistoryOfTrace action reward n) =
      realIndexAction hK action reward c (n + 1) := by
  unfold realHistoryIndexAction realIndexAction
  congr 1
  funext arm
  exact realHistoryIndex_finitePairHistoryOfTrace action reward c n arm

end UCB
end BanditRLProof
