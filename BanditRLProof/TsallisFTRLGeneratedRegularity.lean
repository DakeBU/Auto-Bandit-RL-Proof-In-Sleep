import BanditRLProof.TsallisFTRLRecursiveTrajectory

/-!
# Generated half-Tsallis stability regularity

This module discharges integrability assumptions for the generated pure
half-Tsallis stability route.  The finite sampling law cancels the
importance-weight denominator in the conditional absolute moment, while the
simplex contracts uniformly bound the remaining finite sums.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Every supported coordinate of a finite simplex point is at most one. -/
theorem finiteSimplex_apply_le_one
    {Action : Type u} {arms : Finset Action} {p : Action -> Real}
    (hp : FTRL.finiteSimplex arms p) {action : Action}
    (haction : action ∈ arms) :
    p action <= 1 := by
  calc
    p action <= arms.sum p := Finset.single_le_sum hp.1 haction
    _ = 1 := hp.2

/-- Sampling mass cancels the inverse probability in one realized stability
score, leaving a bound by the current and updated selected coordinates. -/
theorem prob_mul_abs_importanceWeightedStabilityScore_le
    {History : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (next : History -> Action -> Action -> Real)
    (history : History) (chosen : Action) (hchosen : chosen ∈ arms)
    (hnextSimplex : FTRL.finiteSimplex arms (next history chosen))
    (hprobPos : 0 < prob history chosen)
    (hloss : 0 <= loss history chosen ∧ loss history chosen <= 1) :
    prob history chosen *
        |importanceWeightedStabilityScore arms prob loss next (history, chosen)| <=
      prob history chosen + next history chosen chosen := by
  have hprobNonneg : 0 <= prob history chosen := hprobPos.le
  have hnextNonneg : 0 <= next history chosen chosen :=
    hnextSimplex.1 chosen hchosen
  have hprobNe : prob history chosen ≠ 0 := ne_of_gt hprobPos
  have hcurrent :
      FTRL.linearLoss arms (prob history)
          (Exp3.importanceWeightedLoss (prob history) (loss history) chosen) =
        loss history chosen := by
    simpa [FTRL.linearLoss, Exp3.mixedImportanceWeightedLoss] using
      (Exp3.mixedImportanceWeightedLoss_eq_selectedLoss
        arms (prob history) (loss history) chosen hchosen hprobNe)
  have hupdated :
      FTRL.linearLoss arms (next history chosen)
          (Exp3.importanceWeightedLoss (prob history) (loss history) chosen) =
        next history chosen chosen *
          (loss history chosen / prob history chosen) := by
    unfold FTRL.linearLoss
    rw [Finset.sum_eq_single chosen]
    · simp [Exp3.importanceWeightedLoss]
    · intro action haction hne
      simp [Exp3.importanceWeightedLoss, Ne.symm hne]
    · exact fun hnotmem => (hnotmem hchosen).elim
  have hweighted :
      prob history chosen *
          (loss history chosen -
            next history chosen chosen *
              (loss history chosen / prob history chosen)) =
        prob history chosen * loss history chosen -
          next history chosen chosen * loss history chosen := by
    field_simp
  rw [importanceWeightedStabilityScore, hcurrent, hupdated]
  calc
    prob history chosen *
        |loss history chosen -
          next history chosen chosen *
            (loss history chosen / prob history chosen)| =
      |prob history chosen *
        (loss history chosen -
          next history chosen chosen *
            (loss history chosen / prob history chosen))| := by
        rw [abs_mul, abs_of_nonneg hprobNonneg]
    _ = |prob history chosen * loss history chosen -
          next history chosen chosen * loss history chosen| := by
        rw [hweighted]
    _ <= |prob history chosen * loss history chosen| +
          |next history chosen chosen * loss history chosen| := by
        simpa using (_root_.abs_sub_le
          (prob history chosen * loss history chosen) 0
          (next history chosen chosen * loss history chosen))
    _ = prob history chosen * loss history chosen +
          next history chosen chosen * loss history chosen := by
        rw [abs_of_nonneg (mul_nonneg hprobNonneg hloss.1),
          abs_of_nonneg (mul_nonneg hnextNonneg hloss.1)]
    _ <= prob history chosen + next history chosen chosen := by
        nlinarith

/-- Every real-valued function is integrable under a finite action law. -/
theorem integrable_finiteActionMeasure
    {Action : Type u} [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (arms : Finset Action) (prob : Action -> Real) (f : Action -> Real) :
    Integrable f (Exp3.finiteActionMeasure arms prob) := by
  rw [Exp3.finiteActionMeasure]
  refine integrable_finset_sum_measure.2 fun action haction => ?_
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- A measurable one-round stability score is automatically integrable under
its finite sampling kernel.  No uniform lower probability floor is needed. -/
theorem integrable_importanceWeightedStabilityScore_finiteActionKernel
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (historyMu : Measure History) [IsFiniteMeasure historyMu]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (next : History -> Action -> Action -> Real)
    (source : Exp3.MeasurableFiniteActionDistribution arms prob)
    (hprobPos : forall history action, action ∈ arms ->
      0 < prob history action)
    (hnextSimplex : forall history chosen, chosen ∈ arms ->
      FTRL.finiteSimplex arms (next history chosen))
    (hloss : forall history action, action ∈ arms ->
      0 <= loss history action ∧ loss history action <= 1)
    (hscore : Measurable
      (importanceWeightedStabilityScore arms prob loss next)) :
    Integrable (importanceWeightedStabilityScore arms prob loss next)
      (historyMu ⊗ₘ Exp3.finiteActionKernel arms prob source) := by
  let stability := importanceWeightedStabilityScore arms prob loss next
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
  have hsumBound (history : History) :
      arms.sum (fun chosen =>
          prob history chosen * |stability (history, chosen)|) <=
        1 + (arms.card : Real) := by
    calc
      arms.sum (fun chosen =>
          prob history chosen * |stability (history, chosen)|) <=
        arms.sum (fun chosen =>
          prob history chosen + next history chosen chosen) := by
            exact Finset.sum_le_sum fun chosen hchosen =>
              prob_mul_abs_importanceWeightedStabilityScore_le
                arms prob loss next history chosen hchosen
                (hnextSimplex history chosen hchosen)
                (hprobPos history chosen hchosen)
                (hloss history chosen hchosen)
      _ = arms.sum (prob history) +
          arms.sum (fun chosen => next history chosen chosen) := by
            rw [Finset.sum_add_distrib]
      _ <= 1 + arms.sum (fun _chosen => (1 : Real)) := by
            rw [(source.distribution history).sum_eq_one]
            have hnextSum := Finset.sum_le_sum fun chosen hchosen =>
              finiteSimplex_apply_le_one
                (hnextSimplex history chosen hchosen) hchosen
            linarith
      _ = 1 + (arms.card : Real) := by simp
  have hsumIntegrable : Integrable (fun history => arms.sum (fun chosen =>
      prob history chosen * |stability (history, chosen)|)) historyMu := by
    refine Integrable.of_bound hsumMeasurable.aestronglyMeasurable
      (1 + (arms.card : Real)) ?_
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

/-- The half-power stability budget is uniformly bounded and hence integrable
under every finite history measure. -/
theorem integrable_halfPowerStabilityBound_of_finiteSimplex
    {History : Type u} {Action : Type v} [MeasurableSpace History]
    (historyMu : Measure History) [IsFiniteMeasure historyMu]
    (arms : Finset Action) (eta : Real)
    (prob : History -> Action -> Real)
    (source : Exp3.MeasurableFiniteActionDistribution arms prob) :
    Integrable (halfPowerStabilityBound arms eta prob) historyMu := by
  have hmeasurable : Measurable (halfPowerStabilityBound arms eta prob) := by
    unfold halfPowerStabilityBound powerSum
    exact measurable_const.mul
      (Finset.measurable_sum arms fun action haction =>
        (Real.continuous_rpow_const (by norm_num :
          (0 : Real) <= (1 / 2 : Real))).measurable.comp
            (source.measurable_prob action haction))
  refine Integrable.of_bound hmeasurable.aestronglyMeasurable
    (2 * |eta| * (arms.card : Real)) ?_
  exact Filter.Eventually.of_forall fun history => by
    have hpowerNonneg : 0 <= powerSum arms (1 / 2 : Real) (prob history) :=
      powerSum_nonneg_of_finiteSimplex arms (1 / 2 : Real) (prob history)
        ⟨(source.distribution history).nonneg,
          (source.distribution history).sum_eq_one⟩
    have hpowerLe :
        powerSum arms (1 / 2 : Real) (prob history) <=
          (arms.card : Real) := by
      unfold powerSum
      calc
        arms.sum (fun action => (prob history action) ^ (1 / 2 : Real)) <=
            arms.sum (fun _action => (1 : Real)) := by
          exact Finset.sum_le_sum fun action haction =>
            Real.rpow_le_one
              ((source.distribution history).nonneg action haction)
              (finiteSimplex_apply_le_one
                ⟨(source.distribution history).nonneg,
                  (source.distribution history).sum_eq_one⟩ haction)
              (by norm_num)
        _ = (arms.card : Real) := by simp
    rw [halfPowerStabilityBound, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : Real) <= 2),
      abs_of_nonneg hpowerNonneg]
    nlinarith [abs_nonneg eta]

/-- The environment-lifted generated policy is exactly the finite-action
kernel carried by its measurable distribution source. -/
theorem sampledHalfTsallisPolicyAt_eq_finiteActionKernel
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (selector : HalfTsallisFiniteHistorySelectorMeasurability
      arms harms eta) (n : Nat) :
    sampledHalfTsallisPolicyAt (Env := Env) arms harms eta selector n =
      Exp3.finiteActionKernel arms
        (sampledHalfTsallisProbabilityAt (Env := Env) arms harms eta n)
        (sampledHalfTsallisEnvironmentHistoryDistributionSource
          (Env := Env) arms harms eta selector n) := by
  ext input event hevent
  rw [sampledHalfTsallisPolicyAt, Kernel.comap_apply,
    sampledHalfTsallisHistoryAlgorithm_policy,
    Exp3.finiteActionKernel_apply, Exp3.finiteActionKernel_apply]
  rfl

/-- Measurability of the generated stability score now suffices for its
integrability under the generated history/action product law. -/
theorem integrable_sampledHalfTsallisHistoryActionStabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (selector : HalfTsallisFiniteHistorySelectorMeasurability
      arms harms eta)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (hscore : Measurable
      (sampledHalfTsallisHistoryActionStabilityAt
        arms harms eta loss n)) :
    Integrable (sampledHalfTsallisHistoryActionStabilityAt
        arms harms eta loss n)
      (((prior ⊗ₘ sampledHalfTsallisTrajectoryKernel
          arms harms eta selector loss.environment).map
          (sampledHalfTsallisHistoryAt n)) ⊗ₘ
        sampledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector n) := by
  rw [sampledHalfTsallisPolicyAt_eq_finiteActionKernel]
  apply integrable_importanceWeightedStabilityScore_finiteActionKernel
    ((prior ⊗ₘ sampledHalfTsallisTrajectoryKernel
      arms harms eta selector loss.environment).map
      (sampledHalfTsallisHistoryAt n))
    arms
    (sampledHalfTsallisProbabilityAt (Env := Env) arms harms eta n)
    (sampledHalfTsallisPredictableLossAt loss n)
    (sampledHalfTsallisUpdatedAt arms harms eta loss n)
    (sampledHalfTsallisEnvironmentHistoryDistributionSource
      (Env := Env) arms harms eta selector n)
  · intro history action haction
    exact isRegularizedMinimizer_pos arms eta
      (sampledHalfTsallisScoreAt arms harms eta n history)
      (sampledHalfTsallisProbabilityAt arms harms eta n history)
      (halfTsallisMinimizer_isRegularizedMinimizer arms harms eta
        (sampledHalfTsallisScoreAt arms harms eta n history))
      action haction
  · intro history chosen hchosen
    exact (halfTsallisUpdatedMinimizer_isRegularizedMinimizer
      arms harms eta
      (sampledHalfTsallisScoreAt arms harms eta n history)
      (sampledHalfTsallisPredictableLossAt loss n history) chosen).1
  · intro history action _haction
    exact loss.successor_mem_unitInterval n history.1 history.2 action
  · exact hscore

/-- The generated half-power budget is automatically integrable under every
generated history marginal. -/
theorem integrable_sampledHalfTsallisHalfPowerBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (selector : HalfTsallisFiniteHistorySelectorMeasurability
      arms harms eta)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat) :
    Integrable (sampledHalfTsallisHalfPowerBoundAt (Env := Env)
        arms harms eta n)
      ((prior ⊗ₘ sampledHalfTsallisTrajectoryKernel
          arms harms eta selector loss.environment).map
        (sampledHalfTsallisHistoryAt n)) := by
  apply integrable_halfPowerStabilityBound_of_finiteSimplex
    ((prior ⊗ₘ sampledHalfTsallisTrajectoryKernel
      arms harms eta selector loss.environment).map
      (sampledHalfTsallisHistoryAt n))
    arms eta
    (sampledHalfTsallisProbabilityAt (Env := Env) arms harms eta n)
    (sampledHalfTsallisEnvironmentHistoryDistributionSource
      (Env := Env) arms harms eta selector n)

/-- Generated finite-horizon actual-successor stability with both integrability
contracts discharged.  Stability-score measurability remains the exact
selector/update regularity boundary. -/
theorem integral_sum_sampledHalfTsallisSuccessorStability_le_integral_sum_halfPowerStabilityBound_of_measurable
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (horizon : Nat) (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (heta : 0 < eta)
    (selector : HalfTsallisFiniteHistorySelectorMeasurability
      arms harms eta)
    (loss : Exp3.PredictableLossVector Env Action)
    (hscore : forall n, Measurable
      (sampledHalfTsallisHistoryActionStabilityAt
        arms harms eta loss n)) :
    let mu := prior ⊗ₘ sampledHalfTsallisTrajectoryKernel
      arms harms eta selector loss.environment
    integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledHalfTsallisSuccessorStabilityAt
          arms harms eta loss n sample)) <=
      integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledHalfTsallisHalfPowerBoundAt (Env := Env)
          arms harms eta n (sampledHalfTsallisHistoryAt n sample))) := by
  exact
    integral_sum_sampledHalfTsallisSuccessorStability_le_integral_sum_halfPowerStabilityBound
      prior horizon arms harms eta heta selector loss hscore
      (fun n => integrable_sampledHalfTsallisHistoryActionStabilityAt
        prior arms harms eta selector loss n (hscore n))
      (fun n => integrable_sampledHalfTsallisHalfPowerBoundAt
        prior arms harms eta selector loss n)

end Tsallis
end BanditRLProof
