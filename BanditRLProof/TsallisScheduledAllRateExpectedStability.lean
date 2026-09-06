import BanditRLProof.TsallisScheduledAllTimesExpectedStability

/-!
# Expected scheduled half-Tsallis stability at arbitrary positive rates

This module supplies the coarse branch omitted by the refined scheduled
stability theorem.  Ordinary importance weighting has one-round expected
conjugate-potential stability at most one for every positive local rate.  The
final generated-trajectory theorem combines that fallback with the refined
bound available when the local ABRL rate is at most `1 / 2`.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v w

/-- Comparing the old objective at its minimizer with the updated minimizer
reduces conjugate-potential stability to a difference of linear losses. -/
theorem halfTsallisPotentialStability_le_linearLoss_sub_of_minimizers
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (score probability estimate next : Action -> Real)
    (heta : 0 < eta)
    (hprobabilityMin : FTRL.IsRegularizedMinimizer
      (FTRL.finiteSimplex arms) arms eta
      (negEntropyRegularizer arms (1 / 2 : Real)) score probability)
    (hnextMin : FTRL.IsRegularizedMinimizer
      (FTRL.finiteSimplex arms) arms eta
      (negEntropyRegularizer arms (1 / 2 : Real))
      (fun action => score action + estimate action) next) :
    halfTsallisPotentialStability
        arms eta score probability estimate next <=
      FTRL.linearLoss arms probability estimate -
        FTRL.linearLoss arms next estimate := by
  have hmin := hprobabilityMin.2 next hnextMin.1
  have hobjective :
      FTRL.regularizedObjective arms eta
          (negEntropyRegularizer arms (1 / 2 : Real))
          (fun action => score action + estimate action) next =
        FTRL.regularizedObjective arms eta
            (negEntropyRegularizer arms (1 / 2 : Real)) score next +
          eta * FTRL.linearLoss arms next estimate := by
    unfold FTRL.regularizedObjective
    rw [FTRL.linearLoss_add_right]
    ring
  have hdiv :
      (FTRL.regularizedObjective arms eta
          (negEntropyRegularizer arms (1 / 2 : Real)) score probability -
        FTRL.regularizedObjective arms eta
          (negEntropyRegularizer arms (1 / 2 : Real)) score next) / eta <= 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hmin) heta.le
  unfold halfTsallisPotentialStability halfTsallisPotentialValue
  rw [hobjective]
  calc
    _ =
      FTRL.linearLoss arms probability estimate -
          FTRL.linearLoss arms next estimate +
        (FTRL.regularizedObjective arms eta
            (negEntropyRegularizer arms (1 / 2 : Real)) score probability -
          FTRL.regularizedObjective arms eta
            (negEntropyRegularizer arms (1 / 2 : Real)) score next) / eta := by
      field_simp [ne_of_gt heta]
      ring
    _ <= FTRL.linearLoss arms probability estimate -
        FTRL.linearLoss arms next estimate := by linarith

/-- An ordinary importance-weighted minimizer step is at most one, with no
upper bound on the positive learning rate. -/
theorem halfTsallisPotentialStability_importanceWeightedLoss_le_one_of_minimizers
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (score probability loss next : Action -> Real) (chosen : Action)
    (hchosen : chosen ∈ arms) (heta : 0 < eta)
    (hprobabilityMin : FTRL.IsRegularizedMinimizer
      (FTRL.finiteSimplex arms) arms eta
      (negEntropyRegularizer arms (1 / 2 : Real)) score probability)
    (hnextMin : FTRL.IsRegularizedMinimizer
      (FTRL.finiteSimplex arms) arms eta
      (negEntropyRegularizer arms (1 / 2 : Real))
      (fun action => score action +
        Exp3.importanceWeightedLoss probability loss chosen action) next)
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1) :
    halfTsallisPotentialStability arms eta score probability
        (Exp3.importanceWeightedLoss probability loss chosen) next <= 1 := by
  have hpPos := isRegularizedMinimizer_pos
    arms eta score probability hprobabilityMin
  have hcurrent : FTRL.linearLoss arms probability
      (Exp3.importanceWeightedLoss probability loss chosen) = loss chosen := by
    simpa [FTRL.linearLoss, Exp3.mixedImportanceWeightedLoss] using
      Exp3.mixedImportanceWeightedLoss_eq_selectedLoss
        arms probability loss chosen hchosen (ne_of_gt (hpPos chosen hchosen))
  have hnextNonneg : 0 <= FTRL.linearLoss arms next
      (Exp3.importanceWeightedLoss probability loss chosen) := by
    unfold FTRL.linearLoss
    exact Finset.sum_nonneg fun action haction =>
      mul_nonneg (hnextMin.1.1 action haction)
        (Exp3.importanceWeightedLoss_nonneg
          (hprobabilityMin.1.1 action haction) (hloss action haction).1)
  have hbridge :=
    halfTsallisPotentialStability_le_linearLoss_sub_of_minimizers
      arms eta score probability
      (Exp3.importanceWeightedLoss probability loss chosen) next
      heta hprobabilityMin hnextMin
  rw [hcurrent] at hbridge
  linarith [(hloss chosen hchosen).2]

/-- Averaging the arbitrary-rate pointwise bound under the current simplex
keeps the coarse one-round budget equal to one. -/
theorem sum_prob_mul_halfTsallisPotentialStability_importanceWeightedLoss_le_one_of_minimizers
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (score probability loss : Action -> Real)
    (next : Action -> Action -> Real) (heta : 0 < eta)
    (hprobabilityMin : FTRL.IsRegularizedMinimizer
      (FTRL.finiteSimplex arms) arms eta
      (negEntropyRegularizer arms (1 / 2 : Real)) score probability)
    (hnextMin : forall chosen, chosen ∈ arms ->
      FTRL.IsRegularizedMinimizer
        (FTRL.finiteSimplex arms) arms eta
        (negEntropyRegularizer arms (1 / 2 : Real))
        (fun action => score action +
          Exp3.importanceWeightedLoss probability loss chosen action)
        (next chosen))
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1) :
    arms.sum (fun chosen => probability chosen *
        halfTsallisPotentialStability arms eta score probability
          (Exp3.importanceWeightedLoss probability loss chosen)
          (next chosen)) <= 1 := by
  calc
    arms.sum (fun chosen => probability chosen *
        halfTsallisPotentialStability arms eta score probability
          (Exp3.importanceWeightedLoss probability loss chosen)
          (next chosen)) <=
      arms.sum (fun chosen => probability chosen * 1) := by
        exact Finset.sum_le_sum fun chosen hchosen =>
          mul_le_mul_of_nonneg_left
            (halfTsallisPotentialStability_importanceWeightedLoss_le_one_of_minimizers
              arms eta score probability loss (next chosen) chosen hchosen
              heta hprobabilityMin (hnextMin chosen hchosen) hloss)
            (hprobabilityMin.1.1 chosen hchosen)
    _ = 1 := by simpa using hprobabilityMin.1.2

/-- The finite-action product-law score is integrable for every positive rate.
The absolute-value argument uses nonnegativity of true minimizer steps and the
coarse averaged bound, so no probability floor or upper rate bound appears. -/
theorem integrable_importanceWeightedPotentialStabilityScore_finiteActionKernel_coarse
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (historyMu : Measure History) [IsFiniteMeasure historyMu]
    (arms : Finset Action) (eta : Real)
    (score prob loss : History -> Action -> Real)
    (next : History -> Action -> Action -> Real)
    (source : Exp3.MeasurableFiniteActionDistribution arms prob)
    (heta : 0 < eta)
    (hprobMin : forall history,
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms eta (negEntropyRegularizer arms (1 / 2 : Real))
        (score history) (prob history))
    (hnextMin : forall history chosen, chosen ∈ arms ->
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms eta (negEntropyRegularizer arms (1 / 2 : Real))
        (fun candidate => score history candidate +
          Exp3.importanceWeightedLoss
            (prob history) (loss history) chosen candidate)
        (next history chosen))
    (hloss : forall history action, action ∈ arms ->
      0 <= loss history action ∧ loss history action <= 1)
    (hscore : Measurable
      (importanceWeightedPotentialStabilityScore
        arms eta score prob loss next)) :
    Integrable (importanceWeightedPotentialStabilityScore
      arms eta score prob loss next)
      (historyMu ⊗ₘ Exp3.finiteActionKernel arms prob source) := by
  let stability :=
    importanceWeightedPotentialStabilityScore arms eta score prob loss next
  have hconditional (history : History) : Integrable
      (fun chosen => stability (history, chosen))
      (Exp3.finiteActionKernel arms prob source history) := by
    rw [Exp3.finiteActionKernel_apply]
    exact integrable_finiteActionMeasure arms (prob history)
      (fun chosen => stability (history, chosen))
  have hsumMeasurable : Measurable (fun history => arms.sum (fun chosen =>
      prob history chosen * |stability (history, chosen)|)) := by
    refine Finset.measurable_sum arms fun chosen hchosen => ?_
    exact (source.measurable_prob chosen hchosen).mul
      ((hscore.comp (measurable_id.prodMk measurable_const)).abs)
  have hsumEq (history : History) :
      arms.sum (fun chosen =>
          prob history chosen * |stability (history, chosen)|) =
        arms.sum (fun chosen =>
          prob history chosen * stability (history, chosen)) := by
    apply Finset.sum_congr rfl
    intro chosen hchosen
    rw [abs_of_nonneg]
    exact halfTsallisPotentialStability_nonneg_of_minimizers
      arms eta (score history) (prob history)
      (Exp3.importanceWeightedLoss
        (prob history) (loss history) chosen)
      (next history chosen) heta (hprobMin history)
      (hnextMin history chosen hchosen)
  have hsumBound (history : History) :
      arms.sum (fun chosen =>
          prob history chosen * |stability (history, chosen)|) <= 1 := by
    rw [hsumEq]
    simpa [stability, importanceWeightedPotentialStabilityScore] using
      sum_prob_mul_halfTsallisPotentialStability_importanceWeightedLoss_le_one_of_minimizers
        arms eta (score history) (prob history) (loss history)
        (next history) heta (hprobMin history)
        (hnextMin history) (hloss history)
  have hsumIntegrable : Integrable (fun history => arms.sum (fun chosen =>
      prob history chosen * |stability (history, chosen)|)) historyMu := by
    refine Integrable.of_bound hsumMeasurable.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun history => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact hsumBound history
      · exact Finset.sum_nonneg fun chosen hchosen =>
          mul_nonneg ((source.distribution history).nonneg chosen hchosen)
            (abs_nonneg _)
  apply (Measure.integrable_compProd_iff hscore.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall hconditional
  · have hintegralEq :
        (fun history => integral
          (Exp3.finiteActionKernel arms prob source history)
          (fun chosen => ‖stability (history, chosen)‖)) =
        (fun history => arms.sum (fun chosen =>
          prob history chosen * |stability (history, chosen)|)) := by
      funext history
      rw [Exp3.finiteActionKernel_apply,
        Exp3.integral_finiteActionMeasure_eq_sum arms (prob history)
          (source.distribution history)]
      simp only [Real.norm_eq_abs]
    rw [hintegralEq]
    exact hsumIntegrable

/-- An identified finite conditional action law transports the arbitrary-rate
ordinary-IW bound to a one-round integral inequality with constant budget. -/
theorem integral_importanceWeightedPotentialStabilityScore_le_integral_one_of_condDistrib_of_minimizers
    {Omega : Type u} {History : Type v} {Action : Type w}
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (action : Omega -> Action) (haction : Measurable action)
    (arms : Finset Action) (eta : Real)
    (score prob loss : History -> Action -> Real)
    (next : History -> Action -> Action -> Real)
    (policy : Kernel History Action) [IsMarkovKernel policy]
    (hpolicy : policy =ᵐ[mu.map history]
      fun h => Exp3.finiteActionMeasure arms (prob h))
    (hcond : condDistrib action history mu =ᵐ[mu.map history] policy)
    (heta : 0 < eta)
    (hprobMin : forall h,
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms eta (negEntropyRegularizer arms (1 / 2 : Real))
        (score h) (prob h))
    (hnextMin : forall h chosen, chosen ∈ arms ->
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms eta (negEntropyRegularizer arms (1 / 2 : Real))
        (fun candidate => score h candidate +
          Exp3.importanceWeightedLoss
            (prob h) (loss h) chosen candidate)
        (next h chosen))
    (hloss : forall h candidate, candidate ∈ arms ->
      0 <= loss h candidate ∧ loss h candidate <= 1)
    (hscore : Measurable
      (importanceWeightedPotentialStabilityScore
        arms eta score prob loss next))
    (hIntegrable : Integrable
      (importanceWeightedPotentialStabilityScore
        arms eta score prob loss next)
      (mu.map history ⊗ₘ policy)) :
    integral mu (fun omega =>
        importanceWeightedPotentialStabilityScore
          arms eta score prob loss next (history omega, action omega)) <=
      integral (mu.map history) (fun _ => (1 : Real)) := by
  have hdist : forall h, Exp3.FiniteActionDistribution arms (prob h) := by
    intro h
    exact {
      nonneg := (hprobMin h).1.1
      sum_eq_one := (hprobMin h).1.2
    }
  have htransport :=
    Exp3.integral_historyAction_eq_integral_sum_of_condDistrib_ae_eq_finiteActionMeasure
      mu history hhistory action haction arms prob hdist policy hpolicy hcond
      (importanceWeightedPotentialStabilityScore
        arms eta score prob loss next)
      hscore hIntegrable
  have hpoint : forall h,
      arms.sum (fun chosen => prob h chosen *
        importanceWeightedPotentialStabilityScore
          arms eta score prob loss next (h, chosen)) <= 1 := by
    intro h
    simpa [importanceWeightedPotentialStabilityScore] using
      sum_prob_mul_halfTsallisPotentialStability_importanceWeightedLoss_le_one_of_minimizers
        arms eta (score h) (prob h) (loss h) (next h)
        heta (hprobMin h) (hnextMin h) (hloss h)
  have hsumEq :
      (fun h => integral (policy h) (fun chosen =>
        importanceWeightedPotentialStabilityScore
          arms eta score prob loss next (h, chosen))) =ᵐ[mu.map history]
      fun h => arms.sum (fun chosen => prob h chosen *
        importanceWeightedPotentialStabilityScore
          arms eta score prob loss next (h, chosen)) := by
    filter_upwards [hpolicy] with h hh
    rw [hh, Exp3.integral_finiteActionMeasure_eq_sum
      arms (prob h) (hdist h)]
  have hsumIntegrable : Integrable (fun h =>
      arms.sum (fun chosen => prob h chosen *
        importanceWeightedPotentialStabilityScore
          arms eta score prob loss next (h, chosen)))
      (mu.map history) :=
    hIntegrable.integral_compProd.congr hsumEq
  calc
    integral mu (fun omega =>
        importanceWeightedPotentialStabilityScore
          arms eta score prob loss next (history omega, action omega)) =
      integral (mu.map history) (fun h =>
        arms.sum (fun chosen => prob h chosen *
          importanceWeightedPotentialStabilityScore
            arms eta score prob loss next (h, chosen))) := htransport
    _ <= integral (mu.map history) (fun _ => (1 : Real)) := by
      exact integral_mono hsumIntegrable (integrable_const 1) hpoint

/-- A generated scheduled successor term is integrable and has coarse
expected budget one at every positive local rate. -/
theorem integral_sampledScheduledHalfTsallisSuccessorPotentialStabilityAtTime_le_one
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (heta : 0 < eta (n + 1)) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample (n + 1)) mu ∧
      integral mu (fun sample =>
          sampledScheduledHalfTsallisPotentialStabilityAtTime
            arms harms eta sample (n + 1)) <=
        integral mu (fun _sample => (1 : Real)) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hhistory : Measurable
      (sampledScheduledHalfTsallisHistoryAt
        (Env := Env) (Action := Action) n) :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have haction : Measurable
      (sampledScheduledHalfTsallisActionAt
        (Env := Env) (Action := Action) n) :=
    measurable_fst.comp
      ((measurable_pi_apply (n + 1)).comp measurable_snd)
  have hpolicy :
      sampledScheduledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n =ᵐ[
        mu.map (sampledScheduledHalfTsallisHistoryAt n)]
        fun input => Exp3.finiteActionMeasure arms
          (sampledScheduledHalfTsallisProbabilityAt
            (Env := Env) arms harms eta n input) := by
    filter_upwards [] with input
    rw [sampledScheduledHalfTsallisPolicyAt_eq_finiteActionKernel,
      Exp3.finiteActionKernel_apply]
  have hcond :
      condDistrib
          (sampledScheduledHalfTsallisActionAt
            (Env := Env) (Action := Action) n)
          (sampledScheduledHalfTsallisHistoryAt n) mu =ᵐ[
        mu.map (sampledScheduledHalfTsallisHistoryAt n)]
        sampledScheduledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n := by
    simpa [mu, sampledScheduledHalfTsallisHistoryAt,
      sampledScheduledHalfTsallisActionAt,
      sampledScheduledHalfTsallisPolicyAt] using
      (sampledScheduledHalfTsallisTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta selector.finiteHistory loss.environment n)
  have hscore : Measurable
      (sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n) :=
    measurable_sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
      arms harms eta loss n
  have hproduct : Integrable
      (sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
      (mu.map (sampledScheduledHalfTsallisHistoryAt n) ⊗ₘ
        sampledScheduledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n) := by
    have hfinite :=
      integrable_importanceWeightedPotentialStabilityScore_finiteActionKernel_coarse
        (mu.map (sampledScheduledHalfTsallisHistoryAt n))
        arms (eta (n + 1))
        (sampledScheduledHalfTsallisScoreAt arms harms eta n)
        (sampledScheduledHalfTsallisProbabilityAt
          (Env := Env) arms harms eta n)
        (sampledScheduledHalfTsallisPredictableLossAt loss n)
        (sampledScheduledHalfTsallisUpdatedAt arms harms eta loss n)
        (sampledScheduledHalfTsallisEnvironmentHistoryDistributionSource
          (Env := Env) arms harms eta selector.finiteHistory n)
        heta
        (fun input => halfTsallisMinimizer_isRegularizedMinimizer
          arms harms (eta (n + 1))
            (sampledScheduledHalfTsallisScoreAt arms harms eta n input))
        (fun input chosen _ =>
          halfTsallisUpdatedMinimizer_isRegularizedMinimizer
            arms harms (eta (n + 1))
            (sampledScheduledHalfTsallisScoreAt arms harms eta n input)
            (sampledScheduledHalfTsallisPredictableLossAt loss n input)
            chosen)
        (fun input candidate _ =>
          loss.successor_mem_unitInterval n input.1 input.2 candidate)
        hscore
    rw [sampledScheduledHalfTsallisPolicyAt_eq_finiteActionKernel
      arms harms eta selector.finiteHistory n]
    simpa [sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt,
      mu, selector] using hfinite
  have hscoreComp : Integrable (fun sample =>
      sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n
        (sampledScheduledHalfTsallisHistoryAt n sample,
          sampledScheduledHalfTsallisActionAt n sample)) mu :=
    integrable_score_comp_history_action_of_condDistrib_generic
      mu (sampledScheduledHalfTsallisHistoryAt n) hhistory
      (sampledScheduledHalfTsallisActionAt n) haction
      (sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
      (sampledScheduledHalfTsallisPolicyAt (Env := Env)
        arms harms eta selector.finiteHistory n)
      hcond hproduct
  have hcanonical :=
    integral_importanceWeightedPotentialStabilityScore_le_integral_one_of_condDistrib_of_minimizers
      mu (sampledScheduledHalfTsallisHistoryAt n) hhistory
      (sampledScheduledHalfTsallisActionAt n) haction
      arms (eta (n + 1))
      (sampledScheduledHalfTsallisScoreAt arms harms eta n)
      (sampledScheduledHalfTsallisProbabilityAt
        (Env := Env) arms harms eta n)
      (sampledScheduledHalfTsallisPredictableLossAt loss n)
      (sampledScheduledHalfTsallisUpdatedAt arms harms eta loss n)
      (sampledScheduledHalfTsallisPolicyAt (Env := Env)
        arms harms eta selector.finiteHistory n)
      hpolicy hcond heta
      (fun input => halfTsallisMinimizer_isRegularizedMinimizer
        arms harms (eta (n + 1))
          (sampledScheduledHalfTsallisScoreAt arms harms eta n input))
      (fun input chosen _ =>
        halfTsallisUpdatedMinimizer_isRegularizedMinimizer
          arms harms (eta (n + 1))
          (sampledScheduledHalfTsallisScoreAt arms harms eta n input)
          (sampledScheduledHalfTsallisPredictableLossAt loss n input)
          chosen)
      (fun input candidate _ =>
        loss.successor_mem_unitInterval n input.1 input.2 candidate)
      hscore hproduct
  have hterm :=
    sampledScheduledHalfTsallisPotentialStabilityAtTime_succ_eq_historyAction_ae
      prior arms harms eta loss n
  dsimp only at hterm
  refine ⟨hscoreComp.congr hterm.symm, ?_⟩
  calc
    integral mu (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample (n + 1)) =
      integral mu (fun sample =>
        sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta loss n
          (sampledScheduledHalfTsallisHistoryAt n sample,
            sampledScheduledHalfTsallisActionAt n sample)) :=
      integral_congr_ae hterm
    _ <= integral (mu.map (sampledScheduledHalfTsallisHistoryAt n))
        (fun _input => (1 : Real)) := by
      simpa [sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt]
        using hcanonical
    _ = integral mu (fun _sample => (1 : Real)) := by
      rw [integral_map hhistory.aemeasurable
        (integrable_const 1).aestronglyMeasurable]

/-- One generated successor round exposes the refined budget directly, rather
than only through a sum whose rates are all assumed small. -/
theorem integral_sampledScheduledHalfTsallisSuccessorPotentialStabilityAtTime_le_refined
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (heta : 0 < eta (n + 1)) (heta_le : eta (n + 1) <= 1 / 2) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample (n + 1)) mu ∧
      Integrable (fun sample =>
        sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta n
          (sampledScheduledHalfTsallisHistoryAt n sample)) mu ∧
      integral mu (fun sample =>
          sampledScheduledHalfTsallisPotentialStabilityAtTime
            arms harms eta sample (n + 1)) <=
        integral mu (fun sample =>
          sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
            (Env := Env) arms harms eta n
            (sampledScheduledHalfTsallisHistoryAt n sample)) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hhistory : Measurable
      (sampledScheduledHalfTsallisHistoryAt
        (Env := Env) (Action := Action) n) :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have haction : Measurable
      (sampledScheduledHalfTsallisActionAt
        (Env := Env) (Action := Action) n) :=
    measurable_fst.comp
      ((measurable_pi_apply (n + 1)).comp measurable_snd)
  have hpolicy :
      sampledScheduledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n =ᵐ[
        mu.map (sampledScheduledHalfTsallisHistoryAt n)]
        fun input => Exp3.finiteActionMeasure arms
          (sampledScheduledHalfTsallisProbabilityAt
            (Env := Env) arms harms eta n input) := by
    filter_upwards [] with input
    rw [sampledScheduledHalfTsallisPolicyAt_eq_finiteActionKernel,
      Exp3.finiteActionKernel_apply]
  have hcond :
      condDistrib
          (sampledScheduledHalfTsallisActionAt
            (Env := Env) (Action := Action) n)
          (sampledScheduledHalfTsallisHistoryAt n) mu =ᵐ[
        mu.map (sampledScheduledHalfTsallisHistoryAt n)]
        sampledScheduledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n := by
    simpa [mu, sampledScheduledHalfTsallisHistoryAt,
      sampledScheduledHalfTsallisActionAt,
      sampledScheduledHalfTsallisPolicyAt] using
      (sampledScheduledHalfTsallisTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta selector.finiteHistory loss.environment n)
  have hscore : Measurable
      (sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n) :=
    measurable_sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
      arms harms eta loss n
  have hproduct : Integrable
      (sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
      (mu.map (sampledScheduledHalfTsallisHistoryAt n) ⊗ₘ
        sampledScheduledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n) := by
    simpa [mu, selector] using
      (integrable_sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        prior arms harms eta loss n heta heta_le)
  have hboundMap : Integrable
      (sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
        (Env := Env) arms harms eta n)
      (mu.map (sampledScheduledHalfTsallisHistoryAt n)) :=
    integrable_sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
      n (mu.map (sampledScheduledHalfTsallisHistoryAt n))
      arms harms eta heta selector.finiteHistory
  have hboundComp : Integrable (fun sample =>
      sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
        (Env := Env) arms harms eta n
        (sampledScheduledHalfTsallisHistoryAt n sample)) mu := by
    simpa [Function.comp_def] using hboundMap.comp_measurable hhistory
  have hcanonical :=
    integral_importanceWeightedPotentialStabilityScore_le_integral_refinedBound_of_condDistrib_of_minimizers
      mu (sampledScheduledHalfTsallisHistoryAt n) hhistory
      (sampledScheduledHalfTsallisActionAt n) haction
      arms (eta (n + 1))
      (sampledScheduledHalfTsallisScoreAt arms harms eta n)
      (sampledScheduledHalfTsallisProbabilityAt
        (Env := Env) arms harms eta n)
      (sampledScheduledHalfTsallisPredictableLossAt loss n)
      (sampledScheduledHalfTsallisUpdatedAt arms harms eta loss n)
      (sampledScheduledHalfTsallisPolicyAt (Env := Env)
        arms harms eta selector.finiteHistory n)
      hpolicy hcond heta heta_le
      (fun input => halfTsallisMinimizer_isRegularizedMinimizer
        arms harms (eta (n + 1))
          (sampledScheduledHalfTsallisScoreAt arms harms eta n input))
      (fun input chosen _ =>
        halfTsallisUpdatedMinimizer_isRegularizedMinimizer
          arms harms (eta (n + 1))
          (sampledScheduledHalfTsallisScoreAt arms harms eta n input)
          (sampledScheduledHalfTsallisPredictableLossAt loss n input)
          chosen)
      (fun input candidate _ =>
        loss.successor_mem_unitInterval n input.1 input.2 candidate)
      hscore hproduct hboundMap
  have hscoreComp : Integrable (fun sample =>
      sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n
        (sampledScheduledHalfTsallisHistoryAt n sample,
          sampledScheduledHalfTsallisActionAt n sample)) mu :=
    integrable_score_comp_history_action_of_condDistrib_generic
      mu (sampledScheduledHalfTsallisHistoryAt n) hhistory
      (sampledScheduledHalfTsallisActionAt n) haction
      (sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
      (sampledScheduledHalfTsallisPolicyAt (Env := Env)
        arms harms eta selector.finiteHistory n)
      hcond hproduct
  have hterm :=
    sampledScheduledHalfTsallisPotentialStabilityAtTime_succ_eq_historyAction_ae
      prior arms harms eta loss n
  dsimp only at hterm
  refine ⟨hscoreComp.congr hterm.symm, hboundComp, ?_⟩
  calc
    integral mu (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample (n + 1)) =
      integral mu (fun sample =>
        sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta loss n
          (sampledScheduledHalfTsallisHistoryAt n sample,
            sampledScheduledHalfTsallisActionAt n sample)) :=
      integral_congr_ae hterm
    _ <= integral (mu.map (sampledScheduledHalfTsallisHistoryAt n))
        (sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta n) := by
      simpa [sampledScheduledHalfTsallisHistoryActionPotentialStabilityAt,
        sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt] using
        hcanonical
    _ = integral mu (fun sample =>
        sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta n
          (sampledScheduledHalfTsallisHistoryAt n sample)) := by
      rw [integral_map hhistory.aemeasurable
        hboundMap.aestronglyMeasurable]

/-- The generated scheduled time-zero term has the same arbitrary-rate coarse
budget as successor terms. -/
theorem integral_sampledScheduledHalfTsallisInitialPotentialStabilityAtTime_le_one
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (heta : 0 < eta 0) (loss : Exp3.PredictableLossVector Env Action) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample 0) mu ∧
      integral mu (fun sample =>
          sampledScheduledHalfTsallisPotentialStabilityAtTime
            arms harms eta sample 0) <=
        integral mu (fun _sample => (1 : Real)) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let algorithm := sampledScheduledHalfTsallisHistoryAlgorithm
    arms harms eta selector.finiteHistory
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.2 0).1
  let score := fun _env : Env => fun _candidate : Action => (0 : Real)
  let prob := fun _env : Env =>
    initialHalfTsallisDistribution arms harms (eta 0)
  let roundLoss := loss.initial
  let next := sampledHalfTsallisInitialUpdatedAt arms harms (eta 0) loss
  let source := initialHalfTsallisEnvironmentDistributionSource
    (Env := Env) arms harms (eta 0)
  let policy := Exp3.finiteActionKernel arms prob source
  have hhistory : Measurable history := measurable_fst
  have haction : Measurable action :=
    measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)
  have hkernel : Kernel.const Env algorithm.initialAction = policy := by
    ext env event hevent
    rw [Kernel.const_apply, Exp3.finiteActionKernel_apply]
    rfl
  have hcond : condDistrib action history mu =ᵐ[mu.map history] policy := by
    have hbase :=
      Exp3.canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action_zero_given_environment
        prior algorithm loss.environment
    rw [hkernel] at hbase
    simpa [mu, algorithm, history, action,
      sampledScheduledHalfTsallisTrajectoryKernel] using hbase
  have hpolicy : policy =ᵐ[mu.map history]
      fun env => Exp3.finiteActionMeasure arms (prob env) :=
    Exp3.finiteActionKernel_ae_eq_finiteActionMeasure
      (mu.map history) arms prob source
  have hprobMin (env : Env) :
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms (eta 0) (negEntropyRegularizer arms (1 / 2 : Real))
        (score env) (prob env) :=
    halfTsallisMinimizer_isRegularizedMinimizer
      arms harms (eta 0) (score env)
  have hnextMin (env : Env) (chosen : Action) (_hchosen : chosen ∈ arms) :
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms (eta 0) (negEntropyRegularizer arms (1 / 2 : Real))
        (fun candidate => score env candidate +
          Exp3.importanceWeightedLoss
            (prob env) (roundLoss env) chosen candidate)
        (next env chosen) := by
    simpa [score, prob, roundLoss, next,
      sampledHalfTsallisInitialUpdatedAt,
      halfTsallisHistoryUpdatedMinimizer] using
      (halfTsallisUpdatedMinimizer_isRegularizedMinimizer
        arms harms (eta 0) (fun _candidate => 0) (loss.initial env) chosen)
  have hloss (env : Env) (candidate : Action) (_hcandidate : candidate ∈ arms) :
      0 <= roundLoss env candidate ∧ roundLoss env candidate <= 1 :=
    loss.initial_mem_unitInterval env candidate
  have hscore : Measurable
      (importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next) := by
    simpa [score, prob, roundLoss, next,
      sampledScheduledHalfTsallisInitialHistoryActionPotentialStability] using
      (measurable_sampledScheduledHalfTsallisInitialHistoryActionPotentialStability
        arms harms eta loss)
  have hproduct : Integrable
      (importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next)
      (mu.map history ⊗ₘ policy) := by
    have hfinite :=
      integrable_importanceWeightedPotentialStabilityScore_finiteActionKernel_coarse
        (mu.map history) arms (eta 0) score prob roundLoss next source
        heta hprobMin hnextMin hloss hscore
    simpa [policy] using hfinite
  have hcanonical :=
    integral_importanceWeightedPotentialStabilityScore_le_integral_one_of_condDistrib_of_minimizers
      mu history hhistory action haction arms (eta 0) score prob roundLoss next
      policy hpolicy hcond heta hprobMin hnextMin hloss hscore hproduct
  have hscoreComp : Integrable (fun sample =>
      importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next
        (history sample, action sample)) mu :=
    integrable_score_comp_history_action_of_condDistrib_generic
      mu history hhistory action haction
      (importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next)
      policy hcond hproduct
  have hterm :=
    sampledScheduledHalfTsallisPotentialStabilityAtTime_zero_eq_initial_ae
      prior arms harms eta loss
  dsimp only at hterm
  have hterm' :
      (fun sample => sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta sample 0) =ᵐ[mu]
      (fun sample => importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next
        (history sample, action sample)) := by
    simpa [mu, selector, history, action, score, prob, roundLoss, next,
      sampledScheduledHalfTsallisInitialHistoryActionPotentialStability] using
      hterm
  refine ⟨hscoreComp.congr hterm'.symm, ?_⟩
  calc
    integral mu (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample 0) =
      integral mu (fun sample =>
        importanceWeightedPotentialStabilityScore
          arms (eta 0) score prob roundLoss next
          (history sample, action sample)) := integral_congr_ae hterm'
    _ <= integral (mu.map history) (fun _env => (1 : Real)) := hcanonical
    _ = integral mu (fun _sample => (1 : Real)) := by
      rw [integral_map hhistory.aemeasurable
        (integrable_const 1).aestronglyMeasurable]

/-- Piecewise successor budget: use the refined expression at small local
rates and the coarse constant otherwise. -/
noncomputable def sampledScheduledHalfTsallisSuccessorAllRatePotentialStabilityBoundAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (n : Nat) (input : Env × History.FinitePairHistory Action Real n) : Real :=
  if eta (n + 1) <= 1 / 2 then
    sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
      arms harms eta n input
  else 1

/-- Piecewise initial budget with the same local-rate threshold. -/
noncomputable def sampledScheduledHalfTsallisInitialAllRatePotentialStabilityBound
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (env : Env) : Real :=
  if eta 0 <= 1 / 2 then
    sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
      arms harms eta env
  else 1

/-- Piecewise budget indexed by the actual scheduled time. -/
noncomputable def sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (sample : Env × ((k : Nat) -> Action × Real)) : Nat -> Real
  | 0 => sampledScheduledHalfTsallisInitialAllRatePotentialStabilityBound
      arms harms eta sample.1
  | n + 1 =>
      sampledScheduledHalfTsallisSuccessorAllRatePotentialStabilityBoundAt
        arms harms eta n (sampledScheduledHalfTsallisHistoryAt n sample)

/-- A successor term and its piecewise all-rate budget are integrable, and the
expected term is bounded by that budget. -/
theorem integral_sampledScheduledHalfTsallisSuccessorPotentialStabilityAtTime_le_allRateBound
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (heta : 0 < eta (n + 1)) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample (n + 1)) mu ∧
      Integrable (fun sample =>
        sampledScheduledHalfTsallisSuccessorAllRatePotentialStabilityBoundAt
          arms harms eta n
          (sampledScheduledHalfTsallisHistoryAt n sample)) mu ∧
      integral mu (fun sample =>
          sampledScheduledHalfTsallisPotentialStabilityAtTime
            arms harms eta sample (n + 1)) <=
        integral mu (fun sample =>
          sampledScheduledHalfTsallisSuccessorAllRatePotentialStabilityBoundAt
            arms harms eta n
            (sampledScheduledHalfTsallisHistoryAt n sample)) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  by_cases heta_le : eta (n + 1) <= 1 / 2
  · have h :=
      integral_sampledScheduledHalfTsallisSuccessorPotentialStabilityAtTime_le_refined
        prior arms harms eta loss n heta heta_le
    dsimp only at h
    have hboundEq :
        (fun sample : Env × ((k : Nat) -> Action × Real) =>
          sampledScheduledHalfTsallisSuccessorAllRatePotentialStabilityBoundAt
            arms harms eta n
            (sampledScheduledHalfTsallisHistoryAt n sample)) =
        (fun sample =>
          sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
            arms harms eta n
            (sampledScheduledHalfTsallisHistoryAt n sample)) := by
      funext sample
      unfold sampledScheduledHalfTsallisSuccessorAllRatePotentialStabilityBoundAt
      rw [if_pos heta_le]
    rw [hboundEq]
    exact h
  · have h :=
      integral_sampledScheduledHalfTsallisSuccessorPotentialStabilityAtTime_le_one
        prior arms harms eta loss n heta
    dsimp only at h
    have hboundEq :
        (fun sample : Env × ((k : Nat) -> Action × Real) =>
          sampledScheduledHalfTsallisSuccessorAllRatePotentialStabilityBoundAt
            arms harms eta n
            (sampledScheduledHalfTsallisHistoryAt n sample)) =
        (fun _sample => (1 : Real)) := by
      funext sample
      unfold sampledScheduledHalfTsallisSuccessorAllRatePotentialStabilityBoundAt
      rw [if_neg heta_le]
    rw [hboundEq]
    exact ⟨h.1, integrable_const 1, h.2⟩

/-- The initial term and its piecewise all-rate budget satisfy the analogous
integrability and expectation contract. -/
theorem integral_sampledScheduledHalfTsallisInitialPotentialStabilityAtTime_le_allRateBound
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (heta : 0 < eta 0) (loss : Exp3.PredictableLossVector Env Action) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample 0) mu ∧
      Integrable (fun sample =>
        sampledScheduledHalfTsallisInitialAllRatePotentialStabilityBound
          arms harms eta sample.1) mu ∧
      integral mu (fun sample =>
          sampledScheduledHalfTsallisPotentialStabilityAtTime
            arms harms eta sample 0) <=
        integral mu (fun sample =>
          sampledScheduledHalfTsallisInitialAllRatePotentialStabilityBound
            arms harms eta sample.1) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  by_cases heta_le : eta 0 <= 1 / 2
  · have h :=
      integral_sampledScheduledHalfTsallisInitialPotentialStabilityAtTime_le_refined
        prior arms harms eta heta heta_le loss
    dsimp only at h
    have hboundMap : Integrable
        (sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
          (Env := Env) arms harms eta) (mu.map Prod.fst) :=
      integrable_sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
        (mu.map Prod.fst) arms harms eta heta
    have hboundComp : Integrable (fun sample =>
        sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
          (Env := Env) arms harms eta sample.1) mu := by
      simpa [Function.comp_def] using
        hboundMap.comp_measurable measurable_fst
    have hboundEq :
        (fun sample : Env × ((k : Nat) -> Action × Real) =>
          sampledScheduledHalfTsallisInitialAllRatePotentialStabilityBound
            arms harms eta sample.1) =
        (fun sample =>
          sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
            arms harms eta sample.1) := by
      funext sample
      unfold sampledScheduledHalfTsallisInitialAllRatePotentialStabilityBound
      rw [if_pos heta_le]
    rw [hboundEq]
    exact ⟨h.1, hboundComp, h.2⟩
  · have h :=
      integral_sampledScheduledHalfTsallisInitialPotentialStabilityAtTime_le_one
        prior arms harms eta heta loss
    dsimp only at h
    have hboundEq :
        (fun sample : Env × ((k : Nat) -> Action × Real) =>
          sampledScheduledHalfTsallisInitialAllRatePotentialStabilityBound
            arms harms eta sample.1) =
        (fun _sample => (1 : Real)) := by
      funext sample
      unfold sampledScheduledHalfTsallisInitialAllRatePotentialStabilityBound
      rw [if_neg heta_le]
    rw [hboundEq]
    exact ⟨h.1, integrable_const 1, h.2⟩

/-- Every actual scheduled time has an integrable stability term and an
integrable piecewise all-rate budget, with the corresponding expectation
inequality. -/
theorem integral_sampledScheduledHalfTsallisPotentialStabilityAtTime_le_allRateBound
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action) (t : Nat)
    (heta : 0 < eta t) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample t) mu ∧
      Integrable (fun sample =>
        sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
          arms harms eta sample t) mu ∧
      integral mu (fun sample =>
          sampledScheduledHalfTsallisPotentialStabilityAtTime
            arms harms eta sample t) <=
        integral mu (fun sample =>
          sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
            arms harms eta sample t) := by
  cases t with
  | zero =>
      simpa [sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime]
        using
          (integral_sampledScheduledHalfTsallisInitialPotentialStabilityAtTime_le_allRateBound
            prior arms harms eta heta loss)
  | succ n =>
      simpa [sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime]
        using
          (integral_sampledScheduledHalfTsallisSuccessorPotentialStabilityAtTime_le_allRateBound
            prior arms harms eta loss n heta)

/-- Under positivity of every included local rate, both the exact full
scheduled stability sum and its piecewise all-rate budget are integrable. -/
theorem integrable_sum_sampledScheduledHalfTsallisPotentialStabilityAtTime_allRate
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (horizon : Nat) (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real) (heta : forall t, t <= horizon -> 0 < eta t)
    (loss : Exp3.PredictableLossVector Env Action) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample t)) mu ∧
      Integrable (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
        sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
          arms harms eta sample t)) mu := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hround (t : Nat) (ht : t ∈ Finset.range (horizon + 1)) :=
    integral_sampledScheduledHalfTsallisPotentialStabilityAtTime_le_allRateBound
      prior arms harms eta loss t
        (heta t (by
          have ht' := Finset.mem_range.mp ht
          omega))
  dsimp only at hround
  exact ⟨
    IntegrabilitySums.integrable_finset_sum mu (Finset.range (horizon + 1))
      (fun t sample => sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta sample t)
      (fun t ht => (hround t ht).1),
    IntegrabilitySums.integrable_finset_sum mu (Finset.range (horizon + 1))
      (fun t sample =>
        sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
          arms harms eta sample t)
      (fun t ht => (hround t ht).2.1)⟩

/-!
Full all-rate expected scheduled stability.  Each actual time independently
uses the refined budget when `eta t <= 1 / 2`, and otherwise uses the coarse
constant one.  Unlike the refined-only predecessor, this theorem imposes no
uniform upper bound on the included positive rates.
-/
theorem integral_sum_sampledScheduledHalfTsallisPotentialStabilityAtTime_le_allRateBound
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (horizon : Nat) (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real) (heta : forall t, t <= horizon -> 0 < eta t)
    (loss : Exp3.PredictableLossVector Env Action) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample t)) <=
      integral mu (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
        sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
          arms harms eta sample t)) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hround (t : Nat) (ht : t ∈ Finset.range (horizon + 1)) :=
    integral_sampledScheduledHalfTsallisPotentialStabilityAtTime_le_allRateBound
      prior arms harms eta loss t
        (heta t (by
          have ht' := Finset.mem_range.mp ht
          omega))
  dsimp only at hround
  calc
    integral mu (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample t)) =
      (Finset.range (horizon + 1)).sum (fun t => integral mu (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample t)) := by
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range (horizon + 1)) _
        (fun t ht => (hround t ht).1)
    _ <= (Finset.range (horizon + 1)).sum (fun t => integral mu (fun sample =>
        sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
          arms harms eta sample t)) := by
      exact Finset.sum_le_sum fun t ht => (hround t ht).2.2
    _ = integral mu (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
        sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
          arms harms eta sample t)) := by
      symm
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range (horizon + 1)) _
        (fun t ht => (hround t ht).2.1)

end Tsallis
end BanditRLProof
