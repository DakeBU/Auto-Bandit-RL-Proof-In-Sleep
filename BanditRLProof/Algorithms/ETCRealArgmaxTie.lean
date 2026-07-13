import Mathlib.Data.List.MinMax
import BanditRLProof.Algorithms.ETCRealSourceAdapter

/-!
# Native Real ETC least-encoded argmax and action alignment

This module identifies the strict-update fold used by the native Real ETC
route with the least-encoded maximizing arm selected by the `Nat.find` scheme
used in LML's measurable argmax. It then assembles round-robin exploration, the
commit action, and post-commit persistence into the action equality consumed by
the exact native Real source-law theorem.
-/

namespace BanditRLProof
namespace ETC

open MeasureTheory ProbabilityTheory

private theorem argmax_cons_eq_some_foldl_real_select
    {K : Nat} (scores : Fin K -> Real) (init : Fin K) (l : List (Fin K)) :
    List.argmax scores (init :: l) =
      some (l.foldl
        (fun best arm : Fin K =>
          if scores best < scores arm then arm else best)
        init) := by
  unfold List.argmax
  simp only [List.foldl_cons, List.argAux]
  induction l generalizing init with
  | nil => rfl
  | cons arm rest ih =>
      simp only [List.foldl_cons]
      rw [show List.argAux (fun b c : Fin K => scores c < scores b)
          (some init) arm =
          some (if scores init < scores arm then arm else init) by
        by_cases h : scores init < scores arm
        case pos => simp [List.argAux, h]
        case neg => simp [List.argAux, h]]
      exact ih _

/-- The native strict-update fold is Mathlib's first-occurrence list argmax. -/
theorem realArgmaxCommit_argmax_finRange {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) :
    List.argmax scores (List.finRange K) =
      some (ETC.realArgmaxCommit hK scores) := by
  cases K with
  | zero => omega
  | succ k =>
      rw [List.finRange_succ]
      rw [argmax_cons_eq_some_foldl_real_select]
      simp [ETC.realArgmaxCommit, List.finRange_succ]

/-- Among score maximizers, the native fold chooses the least encoded arm. -/
theorem realArgmaxCommit_encode_le_of_score_le {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) (a : Fin K)
    (hscore : scores (ETC.realArgmaxCommit hK scores) <= scores a) :
    Encodable.encode (ETC.realArgmaxCommit hK scores) <= Encodable.encode a := by
  have harg : Membership.mem (List.argmax scores (List.finRange K))
      (ETC.realArgmaxCommit hK scores) := by
    rw [ETC.realArgmaxCommit_argmax_finRange hK scores]
    simp
  have hidx := List.index_of_argmax harg (List.mem_finRange a) hscore
  simpa only [List.idxOf_finRange] using hidx

/-- A natural number encodes a maximizing arm for the supplied score vector. -/
def RealEncodedArgmaxCandidate {K : Nat} (scores : Fin K -> Real)
    (n : Nat) : Prop :=
  Exists fun a : Fin K =>
    And (n = Encodable.encode a)
      (forall z : Fin K, scores z <= scores a)

theorem exists_realEncodedArgmaxCandidate {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) :
    Exists fun n : Nat => ETC.RealEncodedArgmaxCandidate scores n := by
  refine Exists.intro (Encodable.encode (ETC.realArgmaxCommit hK scores)) ?_
  refine Exists.intro (ETC.realArgmaxCommit hK scores) ?_
  exact And.intro rfl (ETC.realArgmaxCommit_spec hK scores)

/-- The least encoded natural-number witness of a maximizing arm. -/
noncomputable def realLeastEncodedArgmaxIndex {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) : Nat := by
  classical
  exact Nat.find (ETC.exists_realEncodedArgmaxCandidate hK scores)

theorem realLeastEncodedArgmaxIndex_candidate {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) :
    ETC.RealEncodedArgmaxCandidate scores
      (ETC.realLeastEncodedArgmaxIndex hK scores) := by
  classical
  unfold ETC.realLeastEncodedArgmaxIndex
  exact Nat.find_spec (ETC.exists_realEncodedArgmaxCandidate hK scores)

/-- The maximizing arm decoded from the least `Nat.find` witness. -/
noncomputable def realLeastEncodedArgmax {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) : Fin K :=
  Classical.choose (ETC.realLeastEncodedArgmaxIndex_candidate hK scores)

theorem realLeastEncodedArgmax_encode_eq_index {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) :
    Encodable.encode (ETC.realLeastEncodedArgmax hK scores) =
      ETC.realLeastEncodedArgmaxIndex hK scores := by
  exact (Classical.choose_spec
    (ETC.realLeastEncodedArgmaxIndex_candidate hK scores)).1.symm

theorem realLeastEncodedArgmax_spec {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) (a : Fin K) :
    scores a <= scores (ETC.realLeastEncodedArgmax hK scores) := by
  exact (Classical.choose_spec
    (ETC.realLeastEncodedArgmaxIndex_candidate hK scores)).2 a

theorem realLeastEncodedArgmax_encode_le_of_isMax {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) (a : Fin K)
    (ha : forall z : Fin K, scores z <= scores a) :
    Encodable.encode (ETC.realLeastEncodedArgmax hK scores) <=
      Encodable.encode a := by
  classical
  rw [ETC.realLeastEncodedArgmax_encode_eq_index]
  unfold ETC.realLeastEncodedArgmaxIndex
  exact Nat.find_min'
    (ETC.exists_realEncodedArgmaxCandidate hK scores)
    (Exists.intro a (And.intro rfl ha))

/-- The LML-shaped least-encoded selector equals the native strict fold. -/
theorem realLeastEncodedArgmax_eq_realArgmaxCommit {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) :
    ETC.realLeastEncodedArgmax hK scores =
      ETC.realArgmaxCommit hK scores := by
  apply Encodable.encode_injective
  have hleft : Encodable.encode (ETC.realLeastEncodedArgmax hK scores) <=
      Encodable.encode (ETC.realArgmaxCommit hK scores) :=
    ETC.realLeastEncodedArgmax_encode_le_of_isMax hK scores
      (ETC.realArgmaxCommit hK scores)
      (ETC.realArgmaxCommit_spec hK scores)
  have hright : Encodable.encode (ETC.realArgmaxCommit hK scores) <=
      Encodable.encode (ETC.realLeastEncodedArgmax hK scores) :=
    ETC.realArgmaxCommit_encode_le_of_score_le hK scores
      (ETC.realLeastEncodedArgmax hK scores)
      (ETC.realLeastEncodedArgmax_spec hK scores
        (ETC.realArgmaxCommit hK scores))
  exact Nat.le_antisymm hleft hright

/--
Round-robin exploration, least-encoded commit, and persistence determine the
native Real ETC action trace. The boundary is written as `K * m` to match the
upstream ETC behavior lemmas; the local trace uses the definitionally
equivalent `m * K` boundary.
-/
theorem eventually_realExplorationArgmaxAction_eq_of_roundRobin_leastEncodedCommit_persist
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega) (spec : ETC.Spec K)
    (baseCommitArm : Fin K)
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (hactionExplore : forall t, t < K * spec.explorationPulls ->
      Filter.EventuallyEq (ae mu)
        (fun omega => action omega t)
        (fun _omega => ETC.exploreArm spec t))
    (hactionCommit : Filter.EventuallyEq (ae mu)
      (fun omega => action omega (K * spec.explorationPulls))
      (fun omega => ETC.realLeastEncodedArgmax spec.hK
        (fun arm => ETC.realEmpMeanAtExploration spec baseCommitArm
          (reward omega) arm)))
    (hactionPersist : forall t, K * spec.explorationPulls <= t ->
      Filter.EventuallyEq (ae mu)
        (fun omega => action omega t)
        (fun omega => action omega (K * spec.explorationPulls))) :
    Filter.Eventually
      (fun omega => forall t,
        action omega t =
          ETC.realExplorationArgmaxAction spec baseCommitArm
            (reward omega) t)
      (ae mu) := by
  rw [ae_all_iff]
  intro t
  by_cases ht : t < spec.explorationPulls * K
  case pos =>
    have htUpstream : t < K * spec.explorationPulls := by
      simpa [Nat.mul_comm] using ht
    filter_upwards [hactionExplore t htUpstream] with omega homega
    simpa [ETC.realExplorationArgmaxAction,
      ETC.actionWithCommit_eq_exploreArm_of_lt spec
        (ETC.realExplorationArgmaxCommit spec baseCommitArm (reward omega)) ht]
      using homega
  case neg =>
    have hge : spec.explorationPulls * K <= t := Nat.le_of_not_gt ht
    have hgeUpstream : K * spec.explorationPulls <= t := by
      simpa [Nat.mul_comm] using hge
    filter_upwards [hactionPersist t hgeUpstream, hactionCommit]
      with omega hpersist hcommit
    calc
      action omega t = action omega (K * spec.explorationPulls) := hpersist
      _ = ETC.realLeastEncodedArgmax spec.hK
          (fun arm => ETC.realEmpMeanAtExploration spec baseCommitArm
            (reward omega) arm) := hcommit
      _ = ETC.realExplorationArgmaxCommit spec baseCommitArm (reward omega) := by
        simpa [ETC.realExplorationArgmaxCommit] using
          (ETC.realLeastEncodedArgmax_eq_realArgmaxCommit spec.hK
            (fun arm => ETC.realEmpMeanAtExploration spec baseCommitArm
              (reward omega) arm))
      _ = ETC.realExplorationArgmaxAction spec baseCommitArm
          (reward omega) t := by
        symm
        exact ETC.actionWithCommit_eq_commitArm_of_ge spec
          (ETC.realExplorationArgmaxCommit spec baseCommitArm (reward omega)) hge

/--
Exact native Real ETC regret from upstream-shaped feedback laws and the three
ETC action behavior fields. Unlike the lower source adapter, callers do not
provide a preassembled horizon action equality: exploration, least-encoded
commit, and persistence construct it here.
-/
theorem integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib_of_leastEncodedCommit_persist
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    [ProbabilityTheory.IsMarkovKernel nu]
    (sigma2 : NNReal)
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm))
    (hm : 0 < spec.explorationPulls) (n : Nat)
    (hn : K * spec.explorationPulls <= n)
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (haction : forall t, Measurable (fun omega => action omega t))
    (hreward : forall t, Measurable (fun omega => reward omega t))
    (hactionExplore : forall t, t < K * spec.explorationPulls ->
      Filter.EventuallyEq (ae mu)
        (fun omega => action omega t)
        (fun _omega => ETC.exploreArm spec t))
    (hactionCommit : Filter.EventuallyEq (ae mu)
      (fun omega => action omega (K * spec.explorationPulls))
      (fun omega => ETC.realLeastEncodedArgmax spec.hK
        (fun arm => ETC.realEmpMeanAtExploration spec
          (ETC.realKernelBestArm spec.hK nu) (reward omega) arm)))
    (hactionPersist : forall t, K * spec.explorationPulls <= t ->
      Filter.EventuallyEq (ae mu)
        (fun omega => action omega t)
        (fun omega => action omega (K * spec.explorationPulls)))
    (hzero : ProbabilityTheory.condDistrib
        (fun omega => reward omega 0)
        (fun omega => action omega 0) mu =ᵐ[mu.map (fun omega => action omega 0)]
      ProbabilityTheory.Kernel.ofFunOfCountable (fun arm : Fin K => nu arm))
    (hcond : forall i, i < spec.explorationPulls * K - 1 ->
      let fullCondition := fun omega : Omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
      ProbabilityTheory.condDistrib
          (fun omega => reward omega (i + 1))
          fullCondition mu =ᵐ[mu.map fullCondition]
        (RewardKernel.contextIndependentOfActionLaws
          (Context := History.FinitePairHistory (Fin K) Real i)
          (fun arm : Fin K => nu arm)
          (fun _arm => inferInstance)).kernel) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        realKernelGap nu arm *
          ((spec.explorationPulls : Real) +
            ((n - K * spec.explorationPulls : Nat) : Real) *
              Real.exp
                (-(spec.explorationPulls : Real) *
                  (realKernelGap nu arm) ^ 2 /
                    (4 * (sigma2 : Real))))) := by
  apply
    ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib
      mu spec nu sigma2 hsubG hm n hn action reward haction hreward
  case hactionExplore =>
    intro t ht
    exact hactionExplore t (by simpa [Nat.mul_comm] using ht)
  case hzero => exact hzero
  case hcond => exact hcond
  case hactionETC =>
    have hall :=
      ETC.eventually_realExplorationArgmaxAction_eq_of_roundRobin_leastEncodedCommit_persist
        mu spec (ETC.realKernelBestArm spec.hK nu) action reward
          hactionExplore hactionCommit hactionPersist
    filter_upwards [hall] with omega homega
    intro t _ht
    exact homega t

end ETC
end BanditRLProof
