import BanditRLProof.TsallisFTRLConditionalStability
import BanditRLProof.ExpectationBochnerSums

/-!
# Expected finite-horizon half-Tsallis stability

This module sums the one-round conditional half-Tsallis stability theorem over
a finite horizon under a common ambient trajectory measure.  Conditional-law
identification is used both for the one-round inequality and for transporting
product-law integrability back to each realized history/action score.

The theorem is stated for a finite measure as an integral inequality.  Under
a probability measure, this is the usual expected stability bound.

The canonical endpoint still exposes the Markov policy/law identification and
measurability/integrability of the updated stability score.  No measurability
property of `Classical.choose` is inferred.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v w

/-- Product-law integrability transports back to the realized history/action
pair when the kernel is the conditional action law. -/
theorem integrable_importanceWeightedStabilityScore_comp_history_action_of_condDistrib
    {Omega : Type u} {History : Type v} {Action : Type w}
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (action : Omega -> Action) (haction : Measurable action)
    (arms : Finset Action)
    (prob loss : History -> Action -> Real)
    (next : History -> Action -> Action -> Real)
    (policy : Kernel History Action) [IsMarkovKernel policy]
    (hcond : condDistrib action history mu =ᵐ[mu.map history] policy)
    (hIntegrable : Integrable
      (importanceWeightedStabilityScore arms prob loss next)
      (mu.map history ⊗ₘ policy)) :
    Integrable (fun omega =>
      importanceWeightedStabilityScore arms prob loss next
        (history omega, action omega)) mu := by
  have hpair :
      mu.map (fun omega => (history omega, action omega)) =
        mu.map history ⊗ₘ policy :=
    (condDistrib_ae_eq_iff_measure_eq_compProd history
      haction.aemeasurable policy).mp hcond
  have hmap : Integrable
      (importanceWeightedStabilityScore arms prob loss next)
      (mu.map (fun omega => (history omega, action omega))) := by
    rwa [hpair]
  simpa [Function.comp_def] using
    hmap.comp_measurable (hhistory.prodMk haction)

/-- Integrability under a history marginal transports back along the history
map. -/
theorem integrable_halfPowerStabilityBound_comp_history
    {Omega : Type u} {History : Type v} {Action : Type w}
    [MeasurableSpace Omega] [MeasurableSpace History]
    (mu : Measure Omega) (history : Omega -> History)
    (hhistory : Measurable history) (arms : Finset Action) (eta : Real)
    (prob : History -> Action -> Real)
    (hIntegrable : Integrable
      (halfPowerStabilityBound arms eta prob) (mu.map history)) :
    Integrable (fun omega =>
      halfPowerStabilityBound arms eta prob (history omega)) mu := by
  simpa [Function.comp_def] using hIntegrable.comp_measurable hhistory

/--
Expected finite-horizon half-Tsallis stability under identified conditional
action laws and explicit current/update minimizer certificates.

All rounds live on one ambient measure `mu`.  This is the theorem-level bridge
from the one-round sampling-law average to the expected finite stability sum.
-/
theorem integral_sum_importanceWeightedStabilityScore_le_integral_sum_halfPowerStabilityBound_of_condDistrib_of_minimizers
    {Omega : Type u} {History : Type v} {Action : Type w}
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (horizon : Nat) (arms : Finset Action) (eta : Real)
    (history : Nat -> Omega -> History)
    (action : Nat -> Omega -> Action)
    (score prob loss : Nat -> History -> Action -> Real)
    (next : Nat -> History -> Action -> Action -> Real)
    (policy : Nat -> Kernel History Action)
    (hmarkov : forall t, IsMarkovKernel (policy t))
    (hhistory : forall t, Measurable (history t))
    (haction : forall t, Measurable (action t))
    (hpolicy : forall t, policy t =ᵐ[mu.map (history t)]
      fun h => Exp3.finiteActionMeasure arms (prob t h))
    (hcond : forall t,
      condDistrib (action t) (history t) mu =ᵐ[mu.map (history t)] policy t)
    (heta : 0 < eta)
    (hprobMin : forall t h,
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms eta (negEntropyRegularizer arms (1 / 2 : Real))
        (score t h) (prob t h))
    (hnextMin : forall t h chosen, chosen ∈ arms ->
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms eta (negEntropyRegularizer arms (1 / 2 : Real))
        (fun candidate => score t h candidate +
          Exp3.importanceWeightedLoss
            (prob t h) (loss t h) chosen candidate)
        (next t h chosen))
    (hloss : forall t h candidate, candidate ∈ arms ->
      0 <= loss t h candidate ∧ loss t h candidate <= 1)
    (hscore : forall t, Measurable
      (importanceWeightedStabilityScore arms (prob t) (loss t) (next t)))
    (hIntegrable : forall t, Integrable
      (importanceWeightedStabilityScore arms (prob t) (loss t) (next t))
      (mu.map (history t) ⊗ₘ policy t))
    (hboundIntegrable : forall t, Integrable
      (halfPowerStabilityBound arms eta (prob t)) (mu.map (history t))) :
    integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        importanceWeightedStabilityScore arms (prob t) (loss t) (next t)
          (history t omega, action t omega))) <=
      integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        halfPowerStabilityBound arms eta (prob t) (history t omega))) := by
  have hscoreComp : forall t, Integrable (fun omega =>
      importanceWeightedStabilityScore arms (prob t) (loss t) (next t)
        (history t omega, action t omega)) mu := by
    intro t
    letI : IsMarkovKernel (policy t) := hmarkov t
    exact
      integrable_importanceWeightedStabilityScore_comp_history_action_of_condDistrib
        mu (history t) (hhistory t) (action t) (haction t)
        arms (prob t) (loss t) (next t) (policy t) (hcond t)
        (hIntegrable t)
  have hboundComp : forall t, Integrable (fun omega =>
      halfPowerStabilityBound arms eta (prob t) (history t omega)) mu := by
    intro t
    exact integrable_halfPowerStabilityBound_comp_history
      mu (history t) (hhistory t) arms eta (prob t) (hboundIntegrable t)
  have hround : forall t,
      integral mu (fun omega =>
          importanceWeightedStabilityScore arms (prob t) (loss t) (next t)
            (history t omega, action t omega)) <=
        integral mu (fun omega =>
          halfPowerStabilityBound arms eta (prob t) (history t omega)) := by
    intro t
    letI : IsMarkovKernel (policy t) := hmarkov t
    have h :=
      integral_importanceWeightedStabilityScore_le_integral_halfPowerStabilityBound_of_condDistrib_of_minimizers
        mu (history t) (hhistory t) (action t) (haction t)
        arms eta (score t) (prob t) (loss t) (next t) (policy t)
        (hpolicy t) (hcond t) heta (hprobMin t) (hnextMin t)
        (hloss t) (hscore t) (hIntegrable t) (hboundIntegrable t)
    calc
      integral mu (fun omega =>
          importanceWeightedStabilityScore arms (prob t) (loss t) (next t)
            (history t omega, action t omega)) <=
          integral (mu.map (history t))
            (halfPowerStabilityBound arms eta (prob t)) := h
      _ = integral mu (fun omega =>
          halfPowerStabilityBound arms eta (prob t) (history t omega)) := by
        rw [integral_map (hhistory t).aemeasurable
          (hboundIntegrable t).aestronglyMeasurable]
  calc
    integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        importanceWeightedStabilityScore arms (prob t) (loss t) (next t)
          (history t omega, action t omega))) =
      (Finset.range horizon).sum (fun t => integral mu (fun omega =>
        importanceWeightedStabilityScore arms (prob t) (loss t) (next t)
          (history t omega, action t omega))) := by
        exact ExpectationBochnerSums.integral_finset_sum mu
          (Finset.range horizon) (fun t omega =>
            importanceWeightedStabilityScore arms (prob t) (loss t) (next t)
              (history t omega, action t omega))
          (fun t _ => hscoreComp t)
    _ <= (Finset.range horizon).sum (fun t => integral mu (fun omega =>
        halfPowerStabilityBound arms eta (prob t) (history t omega))) := by
      exact Finset.sum_le_sum fun t _ => hround t
    _ = integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        halfPowerStabilityBound arms eta (prob t) (history t omega)) ) := by
      symm
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range horizon) (fun t omega =>
          halfPowerStabilityBound arms eta (prob t) (history t omega))
        (fun t _ => hboundComp t)

/-- Canonical half-Tsallis finite-horizon expected stability theorem.  The
current and updated minimizer certificates are internal; selector and score
regularity remain explicit. -/
theorem integral_sum_halfTsallisHistoryStability_le_integral_sum_halfPowerStabilityBound
    {Omega : Type u} {History : Type v} {Action : Type w}
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (horizon : Nat) (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (history : Nat -> Omega -> History)
    (action : Nat -> Omega -> Action)
    (score loss : Nat -> History -> Action -> Real)
    (policy : Nat -> Kernel History Action)
    (hmarkov : forall t, IsMarkovKernel (policy t))
    (hhistory : forall t, Measurable (history t))
    (haction : forall t, Measurable (action t))
    (hpolicy : forall t, policy t =ᵐ[mu.map (history t)] fun h =>
      Exp3.finiteActionMeasure arms
        (halfTsallisHistoryMinimizer arms harms eta (score t) h))
    (hcond : forall t,
      condDistrib (action t) (history t) mu =ᵐ[mu.map (history t)] policy t)
    (heta : 0 < eta)
    (hloss : forall t h candidate, candidate ∈ arms ->
      0 <= loss t h candidate ∧ loss t h candidate <= 1)
    (hscore : forall t, Measurable
      (importanceWeightedStabilityScore arms
        (halfTsallisHistoryMinimizer arms harms eta (score t)) (loss t)
        (halfTsallisHistoryUpdatedMinimizer
          arms harms eta (score t) (loss t))))
    (hIntegrable : forall t, Integrable
      (importanceWeightedStabilityScore arms
        (halfTsallisHistoryMinimizer arms harms eta (score t)) (loss t)
        (halfTsallisHistoryUpdatedMinimizer
          arms harms eta (score t) (loss t)))
      (mu.map (history t) ⊗ₘ policy t))
    (hboundIntegrable : forall t, Integrable
      (halfPowerStabilityBound arms eta
        (halfTsallisHistoryMinimizer arms harms eta (score t)))
      (mu.map (history t))) :
    integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        importanceWeightedStabilityScore arms
          (halfTsallisHistoryMinimizer arms harms eta (score t)) (loss t)
          (halfTsallisHistoryUpdatedMinimizer
            arms harms eta (score t) (loss t))
          (history t omega, action t omega))) <=
      integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        halfPowerStabilityBound arms eta
          (halfTsallisHistoryMinimizer arms harms eta (score t))
          (history t omega))) := by
  exact
    integral_sum_importanceWeightedStabilityScore_le_integral_sum_halfPowerStabilityBound_of_condDistrib_of_minimizers
      mu horizon arms eta history action score
      (fun t => halfTsallisHistoryMinimizer arms harms eta (score t))
      loss
      (fun t => halfTsallisHistoryUpdatedMinimizer
        arms harms eta (score t) (loss t))
      policy hmarkov hhistory haction hpolicy hcond heta
      (fun t h => halfTsallisMinimizer_isRegularizedMinimizer
        arms harms eta (score t h))
      (fun t h chosen _ =>
        halfTsallisUpdatedMinimizer_isRegularizedMinimizer
          arms harms eta (score t h) (loss t h) chosen)
      hloss hscore hIntegrable hboundIntegrable

/-- The realized FTRL stability term using the next round's current
half-Tsallis selector. -/
noncomputable def halfTsallisSuccessorStabilityScore
    {Omega : Type u} {History : Type v} {Action : Type w}
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (history : Nat -> Omega -> History) (action : Nat -> Omega -> Action)
    (score loss : Nat -> History -> Action -> Real)
    (t : Nat) (omega : Omega) : Real :=
  let prob := halfTsallisHistoryMinimizer
    arms harms eta (score t) (history t omega)
  let estimatedLoss := Exp3.importanceWeightedLoss prob
    (loss t (history t omega)) (action t omega)
  FTRL.linearLoss arms prob estimatedLoss -
    FTRL.linearLoss arms
      (halfTsallisHistoryMinimizer
        arms harms eta (score (t + 1)) (history (t + 1) omega))
      estimatedLoss

/--
Expected finite-horizon bound for the actual successor stability sum.

The score recursion identifies the next round's current selector with the
importance-weighted updated selector from the current round.  This closes the
action-dependent successor alignment without claiming it pathwise absent the
explicit recursion contract.
-/
theorem integral_sum_halfTsallisSuccessorStability_le_integral_sum_halfPowerStabilityBound_of_score_succ
    {Omega : Type u} {History : Type v} {Action : Type w}
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (horizon : Nat) (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (history : Nat -> Omega -> History)
    (action : Nat -> Omega -> Action)
    (score loss : Nat -> History -> Action -> Real)
    (policy : Nat -> Kernel History Action)
    (hmarkov : forall t, IsMarkovKernel (policy t))
    (hhistory : forall t, Measurable (history t))
    (haction : forall t, Measurable (action t))
    (hpolicy : forall t, policy t =ᵐ[mu.map (history t)] fun h =>
      Exp3.finiteActionMeasure arms
        (halfTsallisHistoryMinimizer arms harms eta (score t) h))
    (hcond : forall t,
      condDistrib (action t) (history t) mu =ᵐ[mu.map (history t)] policy t)
    (heta : 0 < eta)
    (hloss : forall t h candidate, candidate ∈ arms ->
      0 <= loss t h candidate ∧ loss t h candidate <= 1)
    (hscoreSucc : forall t omega,
      score (t + 1) (history (t + 1) omega) = fun candidate =>
        score t (history t omega) candidate +
          Exp3.importanceWeightedLoss
            (halfTsallisHistoryMinimizer
              arms harms eta (score t) (history t omega))
            (loss t (history t omega)) (action t omega) candidate)
    (hscore : forall t, Measurable
      (importanceWeightedStabilityScore arms
        (halfTsallisHistoryMinimizer arms harms eta (score t)) (loss t)
        (halfTsallisHistoryUpdatedMinimizer
          arms harms eta (score t) (loss t))))
    (hIntegrable : forall t, Integrable
      (importanceWeightedStabilityScore arms
        (halfTsallisHistoryMinimizer arms harms eta (score t)) (loss t)
        (halfTsallisHistoryUpdatedMinimizer
          arms harms eta (score t) (loss t)))
      (mu.map (history t) ⊗ₘ policy t))
    (hboundIntegrable : forall t, Integrable
      (halfPowerStabilityBound arms eta
        (halfTsallisHistoryMinimizer arms harms eta (score t)))
      (mu.map (history t))) :
    integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        halfTsallisSuccessorStabilityScore
          arms harms eta history action score loss t omega)) <=
      integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        halfPowerStabilityBound arms eta
          (halfTsallisHistoryMinimizer arms harms eta (score t))
          (history t omega))) := by
  have hbase :=
    integral_sum_halfTsallisHistoryStability_le_integral_sum_halfPowerStabilityBound
      mu horizon arms harms eta history action score loss policy
      hmarkov hhistory haction hpolicy hcond heta hloss
      hscore hIntegrable hboundIntegrable
  calc
    integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        halfTsallisSuccessorStabilityScore
          arms harms eta history action score loss t omega)) =
      integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        importanceWeightedStabilityScore arms
          (halfTsallisHistoryMinimizer arms harms eta (score t)) (loss t)
          (halfTsallisHistoryUpdatedMinimizer
            arms harms eta (score t) (loss t))
          (history t omega, action t omega))) := by
      apply integral_congr_ae
      filter_upwards [] with omega
      apply Finset.sum_congr rfl
      intro t _ht
      have hnext :
          halfTsallisHistoryMinimizer
              arms harms eta (score (t + 1)) (history (t + 1) omega) =
            halfTsallisHistoryUpdatedMinimizer
              arms harms eta (score t) (loss t)
                (history t omega) (action t omega) := by
        simp only [halfTsallisHistoryMinimizer,
          halfTsallisHistoryUpdatedMinimizer, halfTsallisUpdatedMinimizer]
        rw [hscoreSucc t omega]
        simp only [halfTsallisHistoryMinimizer]
      simp only [halfTsallisSuccessorStabilityScore,
        importanceWeightedStabilityScore]
      rw [hnext]
    _ <= integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        halfPowerStabilityBound arms eta
          (halfTsallisHistoryMinimizer arms harms eta (score t))
          (history t omega))) := hbase

end Tsallis
end BanditRLProof
