import BanditRLProof.TsallisConjugatePotentialStability
import BanditRLProof.TsallisFTRLGeneratedMeasurability
import BanditRLProof.Exp3Potential
import BanditRLProof.ExpectationBochnerSums

/-!
# Finite-horizon half-Tsallis conjugate-potential stability

This module transports the compiled ordinary-importance-weighted
conjugate-potential bound through identified finite conditional action laws and
sums it over a finite horizon.  It also records the exact deterministic
potential telescope.  The potential includes the paper-normalizing 1 / eta,
so the process is ready for later cross-learning-rate comparisons.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v w

/-- A time-indexed paper-normalized half-Tsallis potential. -/
noncomputable def halfTsallisPotentialProcess
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (score probability : Nat -> Action -> Real) (t : Nat) : Real :=
  halfTsallisPotentialValue arms eta (score t) (probability t)

/--
Exact fixed-learning-rate finite-horizon telescope for the candidate potential
expression.  When every probability is the corresponding certified minimizer,
this is the constrained-potential telescope.
-/
theorem sum_halfTsallisPotentialStability_eq_linearLoss_sum_add_terminal_sub_initial
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (score probability estimate : Nat -> Action -> Real)
    (T : Nat)
    (hscoreSucc : forall t, t < T ->
      score (t + 1) = fun action => score t action + estimate t action) :
    (Finset.range T).sum (fun t =>
        halfTsallisPotentialStability arms eta
          (score t) (probability t) (estimate t) (probability (t + 1))) =
      (Finset.range T).sum (fun t =>
        FTRL.linearLoss arms (probability t) (estimate t)) +
        halfTsallisPotentialProcess arms eta score probability T -
        halfTsallisPotentialProcess arms eta score probability 0 := by
  have hpotential :
      (Finset.range T).sum (fun t =>
          halfTsallisPotentialValue arms eta
              (fun action => score t action + estimate t action)
              (probability (t + 1)) -
            halfTsallisPotentialValue arms eta
              (score t) (probability t)) =
        (Finset.range T).sum (fun t =>
          halfTsallisPotentialProcess arms eta score probability (t + 1) -
            halfTsallisPotentialProcess arms eta score probability t) := by
    apply Finset.sum_congr rfl
    intro t ht
    unfold halfTsallisPotentialProcess
    rw [hscoreSucc t (Finset.mem_range.mp ht)]
  calc
    (Finset.range T).sum (fun t =>
        halfTsallisPotentialStability arms eta
          (score t) (probability t) (estimate t) (probability (t + 1))) =
      (Finset.range T).sum (fun t =>
          FTRL.linearLoss arms (probability t) (estimate t)) +
        (Finset.range T).sum (fun t =>
          halfTsallisPotentialValue arms eta
              (fun action => score t action + estimate t action)
              (probability (t + 1)) -
            halfTsallisPotentialValue arms eta
              (score t) (probability t)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _ht
      unfold halfTsallisPotentialStability
      ring
    _ = (Finset.range T).sum (fun t =>
          FTRL.linearLoss arms (probability t) (estimate t)) +
        (Finset.range T).sum (fun t =>
          halfTsallisPotentialProcess arms eta score probability (t + 1) -
            halfTsallisPotentialProcess arms eta score probability t) := by
      rw [hpotential]
    _ = (Finset.range T).sum (fun t =>
          FTRL.linearLoss arms (probability t) (estimate t)) +
        halfTsallisPotentialProcess arms eta score probability T -
        halfTsallisPotentialProcess arms eta score probability 0 := by
      rw [Exp3Potential.sum_range_forward_difference]
      ring

/-- The realized one-round conjugate-potential score on a history/action pair. -/
noncomputable def importanceWeightedPotentialStabilityScore
    {History : Type u} {Action : Type v}
    (arms : Finset Action) (eta : Real)
    (score prob loss : History -> Action -> Real)
    (next : History -> Action -> Action -> Real)
    (sample : History × Action) : Real :=
  halfTsallisPotentialStability arms eta
    (score sample.1) (prob sample.1)
    (Exp3.importanceWeightedLoss
      (prob sample.1) (loss sample.1) sample.2)
    (next sample.1 sample.2)

/-- The paper-shaped one-round conditional expectation budget. -/
noncomputable def refinedPotentialStabilityBound
    {History : Type u} {Action : Type v}
    (arms : Finset Action) (eta : Real)
    (prob : History -> Action -> Real) (history : History) : Real :=
  eta * arms.sum (fun action =>
      Real.sqrt (prob history action) * (1 - prob history action)) +
    2 * eta ^ 2

/-- Coordinatewise measurability closes a finite linear-loss sum. -/
theorem measurable_linearLoss_of_coordinatewise
    {History : Type u} {Action : Type v} [MeasurableSpace History]
    (arms : Finset Action) (prob loss : History -> Action -> Real)
    (hprob : forall action, action ∈ arms ->
      Measurable (fun history => prob history action))
    (hloss : forall action, action ∈ arms ->
      Measurable (fun history => loss history action)) :
    Measurable (fun history =>
      FTRL.linearLoss arms (prob history) (loss history)) := by
  unfold FTRL.linearLoss
  exact Finset.measurable_sum arms fun action haction =>
    (hprob action haction).mul (hloss action haction)

/-- The paper-normalized potential is measurable from supported coordinate
measurability of its score and simplex candidate. -/
theorem measurable_halfTsallisPotentialValue
    {History : Type u} {Action : Type v} [MeasurableSpace History]
    (arms : Finset Action) (eta : Real)
    (score probability : History -> Action -> Real)
    (hscore : forall action, action ∈ arms ->
      Measurable (fun history => score history action))
    (hprobability : forall action, action ∈ arms ->
      Measurable (fun history => probability history action)) :
    Measurable (fun history =>
      halfTsallisPotentialValue arms eta
        (score history) (probability history)) := by
  have hlinear := measurable_linearLoss_of_coordinatewise
    arms probability score hprobability hscore
  have hsqrt : Measurable (fun history =>
      arms.sum (fun action => Real.sqrt (probability history action))) :=
    Finset.measurable_sum arms fun action haction =>
      (hprobability action haction).sqrt
  have hobjective : Measurable (fun history =>
      eta * FTRL.linearLoss arms (probability history) (score history) -
        2 * arms.sum (fun action =>
          Real.sqrt (probability history action)) + 2) :=
    ((measurable_const.mul hlinear).sub (measurable_const.mul hsqrt)).add
      measurable_const
  have hformula : (fun history =>
      halfTsallisPotentialValue arms eta
        (score history) (probability history)) =
      fun history =>
        -(eta * FTRL.linearLoss arms (probability history) (score history) -
            2 * arms.sum (fun action =>
              Real.sqrt (probability history action)) + 2) / eta +
          1 / eta := by
    funext history
    rw [halfTsallisPotentialValue,
      regularizedObjective_half_eq]
  rw [hformula]
  exact (hobjective.neg.div measurable_const).add measurable_const

set_option maxHeartbeats 1200000 in
/-- The conjugate-potential score is measurable from supported current score,
probability, loss, and updated-selector coordinates. -/
theorem measurable_importanceWeightedPotentialStabilityScore
    {History : Type u} {Action : Type v}
    [MeasurableSpace History] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (score prob loss : History -> Action -> Real)
    (next : History -> Action -> Action -> Real)
    (hscore : forall candidate, candidate ∈ arms ->
      Measurable (fun history => score history candidate))
    (hprob : forall candidate, candidate ∈ arms ->
      Measurable (fun history => prob history candidate))
    (hloss : forall candidate, candidate ∈ arms ->
      Measurable (fun history => loss history candidate))
    (hnext : forall candidate, candidate ∈ arms ->
      Measurable (fun sample : History × Action =>
        next sample.1 sample.2 candidate)) :
    Measurable (importanceWeightedPotentialStabilityScore
      arms eta score prob loss next) := by
  have hestimate : forall candidate, candidate ∈ arms ->
      Measurable (fun sample : History × Action =>
        Exp3.importanceWeightedLoss (prob sample.1) (loss sample.1)
          sample.2 candidate) := by
    intro candidate hcandidate
    unfold Exp3.importanceWeightedLoss
    refine Measurable.ite ?_
      (((hloss candidate hcandidate).comp measurable_fst).div
        ((hprob candidate hcandidate).comp measurable_fst))
      measurable_const
    simpa only [Set.mem_setOf_eq] using
      measurable_snd (measurableSet_singleton candidate)
  have hcurrentPotential : Measurable (fun sample : History × Action =>
      halfTsallisPotentialValue arms eta
        (score sample.1) (prob sample.1)) :=
    measurable_halfTsallisPotentialValue arms eta
      (fun sample : History × Action => score sample.1)
      (fun sample : History × Action => prob sample.1)
      (fun candidate hcandidate =>
        (hscore candidate hcandidate).comp measurable_fst)
      (fun candidate hcandidate =>
        (hprob candidate hcandidate).comp measurable_fst)
  have hnextPotential : Measurable (fun sample : History × Action =>
      halfTsallisPotentialValue arms eta
        (fun candidate => score sample.1 candidate +
          Exp3.importanceWeightedLoss
            (prob sample.1) (loss sample.1) sample.2 candidate)
        (next sample.1 sample.2)) :=
    measurable_halfTsallisPotentialValue arms eta
      (fun (sample : History × Action) candidate => score sample.1 candidate +
        Exp3.importanceWeightedLoss
          (prob sample.1) (loss sample.1) sample.2 candidate)
      (fun (sample : History × Action) candidate =>
        next sample.1 sample.2 candidate)
      (fun candidate hcandidate =>
        ((hscore candidate hcandidate).comp measurable_fst).add
          (hestimate candidate hcandidate))
      hnext
  have hlinear : Measurable (fun sample : History × Action =>
      FTRL.linearLoss arms (prob sample.1)
        (Exp3.importanceWeightedLoss
          (prob sample.1) (loss sample.1) sample.2)) :=
    measurable_linearLoss_of_coordinatewise arms
      (fun sample : History × Action => prob sample.1)
      (fun sample candidate =>
        Exp3.importanceWeightedLoss
          (prob sample.1) (loss sample.1) sample.2 candidate)
      (fun candidate hcandidate =>
        (hprob candidate hcandidate).comp measurable_fst)
      hestimate
  unfold importanceWeightedPotentialStabilityScore
  unfold halfTsallisPotentialStability
  exact hlinear.add hnextPotential |>.sub hcurrentPotential

/-- The refined one-round budget is measurable from supported probability
coordinates. -/
theorem measurable_refinedPotentialStabilityBound
    {History : Type u} {Action : Type v} [MeasurableSpace History]
    (arms : Finset Action) (eta : Real)
    (prob : History -> Action -> Real)
    (hprob : forall action, action ∈ arms ->
      Measurable (fun history => prob history action)) :
    Measurable (refinedPotentialStabilityBound arms eta prob) := by
  unfold refinedPotentialStabilityBound
  exact (measurable_const.mul
    (Finset.measurable_sum arms fun action haction =>
      (hprob action haction).sqrt.mul
        (measurable_const.sub (hprob action haction)))).add measurable_const

/-- A true minimizer-to-minimizer potential step is nonnegative. -/
theorem halfTsallisPotentialStability_nonneg_of_minimizers
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
    0 <= halfTsallisPotentialStability
      arms eta score probability estimate next := by
  have hmin := hnextMin.2 probability hprobabilityMin.1
  have hobjective :
      FTRL.regularizedObjective arms eta
          (negEntropyRegularizer arms (1 / 2 : Real))
          (fun action => score action + estimate action) probability =
        FTRL.regularizedObjective arms eta
          (negEntropyRegularizer arms (1 / 2 : Real))
          score probability +
        eta * FTRL.linearLoss arms probability estimate := by
    unfold FTRL.regularizedObjective
    rw [FTRL.linearLoss_add_right]
    ring
  have hminDiv := div_le_div_of_nonneg_right hmin heta.le
  unfold halfTsallisPotentialStability halfTsallisPotentialValue
  rw [hobjective] at hminDiv
  have heta_ne : eta ≠ 0 := ne_of_gt heta
  rw [add_div, mul_div_cancel_left₀ _ heta_ne] at hminDiv
  calc
    0 <=
        FTRL.regularizedObjective arms eta
            (negEntropyRegularizer arms (1 / 2 : Real)) score probability / eta +
          FTRL.linearLoss arms probability estimate -
          FTRL.regularizedObjective arms eta
            (negEntropyRegularizer arms (1 / 2 : Real))
            (fun action => score action + estimate action) next / eta :=
      sub_nonneg.mpr hminDiv
    _ = FTRL.linearLoss arms probability estimate +
          (-FTRL.regularizedObjective arms eta
              (negEntropyRegularizer arms (1 / 2 : Real))
              (fun action => score action + estimate action) next / eta + 1 / eta) -
          (-FTRL.regularizedObjective arms eta
              (negEntropyRegularizer arms (1 / 2 : Real)) score probability / eta +
            1 / eta) := by ring

/-- The refined budget is uniformly integrable under a finite history measure. -/
theorem integrable_refinedPotentialStabilityBound_of_finiteSimplex
    {History : Type u} {Action : Type v} [MeasurableSpace History]
    (historyMu : Measure History) [IsFiniteMeasure historyMu]
    (arms : Finset Action) (eta : Real)
    (prob : History -> Action -> Real)
    (source : Exp3.MeasurableFiniteActionDistribution arms prob)
    (heta : 0 < eta) :
    Integrable (refinedPotentialStabilityBound arms eta prob) historyMu := by
  have hmeasurable := measurable_refinedPotentialStabilityBound
    arms eta prob source.measurable_prob
  refine Integrable.of_bound hmeasurable.aestronglyMeasurable
    (eta * (arms.card : Real) + 2 * eta ^ 2) ?_
  exact Filter.Eventually.of_forall fun history => by
    have hsimplex : FTRL.finiteSimplex arms (prob history) := {
      left := (source.distribution history).nonneg
      right := (source.distribution history).sum_eq_one
    }
    have hsumNonneg : 0 <= arms.sum (fun action =>
        Real.sqrt (prob history action) * (1 - prob history action)) := by
      exact Finset.sum_nonneg fun action haction =>
        mul_nonneg (Real.sqrt_nonneg _)
          (sub_nonneg.mpr (finiteSimplex_apply_le_one
            hsimplex haction))
    have hsumLe : arms.sum (fun action =>
        Real.sqrt (prob history action) * (1 - prob history action)) <=
        (arms.card : Real) := by
      calc
        arms.sum (fun action =>
            Real.sqrt (prob history action) * (1 - prob history action)) <=
          arms.sum (fun _action => (1 : Real)) := by
            apply Finset.sum_le_sum
            intro action haction
            have hpNonneg := hsimplex.1 action haction
            have hpLe := finiteSimplex_apply_le_one
              hsimplex haction
            have hsqrtLe : Real.sqrt (prob history action) <= 1 :=
              (Real.sqrt_le_one).2 hpLe
            have honeSub : 0 <= 1 - prob history action := by linarith
            calc
              Real.sqrt (prob history action) *
                    (1 - prob history action) <=
                  1 * (1 - prob history action) :=
                mul_le_mul_of_nonneg_right hsqrtLe honeSub
              _ <= 1 := by linarith
        _ = (arms.card : Real) := by simp
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · unfold refinedPotentialStabilityBound
      nlinarith
    · unfold refinedPotentialStabilityBound
      nlinarith [sq_nonneg eta]

/-- Measurability plus exact minimizer certificates give integrability of the
potential score under the finite sampling kernel, without a probability floor. -/
theorem integrable_importanceWeightedPotentialStabilityScore_finiteActionKernel
    {History : Type u} {Action : Type v}
    [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (historyMu : Measure History) [IsFiniteMeasure historyMu]
    (arms : Finset Action) (eta : Real)
    (score prob loss : History -> Action -> Real)
    (next : History -> Action -> Action -> Real)
    (source : Exp3.MeasurableFiniteActionDistribution arms prob)
    (heta : 0 < eta) (heta_le : eta <= 1 / 2)
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
          prob history chosen * |stability (history, chosen)|) <=
        eta * (arms.card : Real) + 2 * eta ^ 2 := by
    rw [hsumEq]
    have hrefined :=
      sum_prob_mul_halfTsallisPotentialStability_importanceWeightedLoss_le_refined_of_minimizers
        arms eta (score history) (prob history) (loss history)
        (next history) heta heta_le (hprobMin history)
        (hnextMin history) (hloss history)
    have hsimplex : FTRL.finiteSimplex arms (prob history) := {
      left := (source.distribution history).nonneg
      right := (source.distribution history).sum_eq_one
    }
    have hsumLe : arms.sum (fun action =>
        Real.sqrt (prob history action) * (1 - prob history action)) <=
        (arms.card : Real) := by
      calc
        arms.sum (fun action =>
            Real.sqrt (prob history action) * (1 - prob history action)) <=
          arms.sum (fun _action => (1 : Real)) := by
            apply Finset.sum_le_sum
            intro action haction
            have hpNonneg := hsimplex.1 action haction
            have hpLe := finiteSimplex_apply_le_one
              hsimplex haction
            have hsqrtLe : Real.sqrt (prob history action) <= 1 :=
              (Real.sqrt_le_one).2 hpLe
            have honeSub : 0 <= 1 - prob history action := by linarith
            calc
              Real.sqrt (prob history action) *
                    (1 - prob history action) <=
                  1 * (1 - prob history action) :=
                mul_le_mul_of_nonneg_right hsqrtLe honeSub
              _ <= 1 := by linarith
        _ = (arms.card : Real) := by simp
    have hrefined' :
        arms.sum (fun chosen =>
          prob history chosen * stability (history, chosen)) <=
        eta * arms.sum (fun action =>
          Real.sqrt (prob history action) * (1 - prob history action)) +
          2 * eta ^ 2 := by
      simpa [stability, importanceWeightedPotentialStabilityScore] using
        hrefined
    exact hrefined'.trans (by
      have hscaled := mul_le_mul_of_nonneg_left hsumLe heta.le
      linarith)
  have hsumIntegrable : Integrable (fun history => arms.sum (fun chosen =>
      prob history chosen * |stability (history, chosen)|)) historyMu := by
    refine Integrable.of_bound hsumMeasurable.aestronglyMeasurable
      (eta * (arms.card : Real) + 2 * eta ^ 2) ?_
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

/-- Product-law integrability pulls back to a realized history/action pair
when the kernel is an identified conditional action law. -/
theorem integrable_score_comp_history_action_of_condDistrib_generic
    {Omega : Type u} {History : Type v} {Action : Type w}
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (action : Omega -> Action) (haction : Measurable action)
    (score : History × Action -> Real)
    (policy : Kernel History Action) [IsMarkovKernel policy]
    (hcond : condDistrib action history mu =ᵐ[mu.map history] policy)
    (hIntegrable : Integrable score (mu.map history ⊗ₘ policy)) :
    Integrable (fun omega => score (history omega, action omega)) mu := by
  have hpair :
      mu.map (fun omega => (history omega, action omega)) =
        mu.map history ⊗ₘ policy :=
    (condDistrib_ae_eq_iff_measure_eq_compProd history
      haction.aemeasurable policy).mp hcond
  have hmap : Integrable score
      (mu.map (fun omega => (history omega, action omega))) := by
    rwa [hpair]
  simpa [Function.comp_def] using
    hmap.comp_measurable (hhistory.prodMk haction)

/--
An identified finite conditional action law transports the deterministic
ordinary-IW conjugate-potential theorem to a one-round integral inequality.
-/
theorem integral_importanceWeightedPotentialStabilityScore_le_integral_refinedBound_of_condDistrib_of_minimizers
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
    (heta : 0 < eta) (heta_le : eta <= 1 / 2)
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
      (mu.map history ⊗ₘ policy))
    (hboundIntegrable : Integrable
      (refinedPotentialStabilityBound arms eta prob) (mu.map history)) :
    integral mu (fun omega =>
        importanceWeightedPotentialStabilityScore
          arms eta score prob loss next (history omega, action omega)) <=
      integral (mu.map history)
        (refinedPotentialStabilityBound arms eta prob) := by
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
          arms eta score prob loss next (h, chosen)) <=
        refinedPotentialStabilityBound arms eta prob h := by
    intro h
    simpa [importanceWeightedPotentialStabilityScore,
      refinedPotentialStabilityBound] using
      sum_prob_mul_halfTsallisPotentialStability_importanceWeightedLoss_le_refined_of_minimizers
        arms eta (score h) (prob h) (loss h) (next h)
        heta heta_le (hprobMin h) (hnextMin h) (hloss h)
  calc
    integral mu (fun omega =>
        importanceWeightedPotentialStabilityScore
          arms eta score prob loss next (history omega, action omega)) =
      integral (mu.map history) (fun h =>
        arms.sum (fun chosen => prob h chosen *
          importanceWeightedPotentialStabilityScore
            arms eta score prob loss next (h, chosen))) := htransport
    _ <= integral (mu.map history)
        (refinedPotentialStabilityBound arms eta prob) := by
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
      exact integral_mono hsumIntegrable hboundIntegrable hpoint

/--
Finite-horizon expected conjugate-potential stability under identified
conditional action laws and exact current/update minimizer certificates.
-/
theorem integral_sum_importanceWeightedPotentialStabilityScore_le_integral_sum_refinedBound_of_condDistrib_of_minimizers
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
    (heta : 0 < eta) (heta_le : eta <= 1 / 2)
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
      (importanceWeightedPotentialStabilityScore
        arms eta (score t) (prob t) (loss t) (next t)))
    (hIntegrable : forall t, Integrable
      (importanceWeightedPotentialStabilityScore
        arms eta (score t) (prob t) (loss t) (next t))
      (mu.map (history t) ⊗ₘ policy t))
    (hboundIntegrable : forall t, Integrable
      (refinedPotentialStabilityBound arms eta (prob t))
      (mu.map (history t))) :
    integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        importanceWeightedPotentialStabilityScore
          arms eta (score t) (prob t) (loss t) (next t)
          (history t omega, action t omega))) <=
      integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        refinedPotentialStabilityBound arms eta (prob t)
          (history t omega))) := by
  have hscoreComp : forall t, Integrable (fun omega =>
      importanceWeightedPotentialStabilityScore
        arms eta (score t) (prob t) (loss t) (next t)
        (history t omega, action t omega)) mu := by
    intro t
    letI : IsMarkovKernel (policy t) := hmarkov t
    exact
      integrable_score_comp_history_action_of_condDistrib_generic
        mu (history t) (hhistory t) (action t) (haction t)
        (importanceWeightedPotentialStabilityScore
          arms eta (score t) (prob t) (loss t) (next t))
        (policy t) (hcond t) (hIntegrable t)
  have hboundComp : forall t, Integrable (fun omega =>
      refinedPotentialStabilityBound arms eta (prob t)
        (history t omega)) mu := by
    intro t
    simpa [Function.comp_def] using
      (hboundIntegrable t).comp_measurable (hhistory t)
  have hround : forall t,
      integral mu (fun omega =>
        importanceWeightedPotentialStabilityScore
          arms eta (score t) (prob t) (loss t) (next t)
          (history t omega, action t omega)) <=
      integral mu (fun omega =>
        refinedPotentialStabilityBound arms eta (prob t)
          (history t omega)) := by
    intro t
    letI : IsMarkovKernel (policy t) := hmarkov t
    have h :=
      integral_importanceWeightedPotentialStabilityScore_le_integral_refinedBound_of_condDistrib_of_minimizers
        mu (history t) (hhistory t) (action t) (haction t)
        arms eta (score t) (prob t) (loss t) (next t) (policy t)
        (hpolicy t) (hcond t) heta heta_le (hprobMin t) (hnextMin t)
        (hloss t) (hscore t) (hIntegrable t) (hboundIntegrable t)
    calc
      integral mu (fun omega =>
          importanceWeightedPotentialStabilityScore
            arms eta (score t) (prob t) (loss t) (next t)
            (history t omega, action t omega)) <=
        integral (mu.map (history t))
          (refinedPotentialStabilityBound arms eta (prob t)) := h
      _ = integral mu (fun omega =>
          refinedPotentialStabilityBound arms eta (prob t)
            (history t omega)) := by
        rw [integral_map (hhistory t).aemeasurable
          (hboundIntegrable t).aestronglyMeasurable]
  calc
    integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        importanceWeightedPotentialStabilityScore
          arms eta (score t) (prob t) (loss t) (next t)
          (history t omega, action t omega))) =
      (Finset.range horizon).sum (fun t => integral mu (fun omega =>
        importanceWeightedPotentialStabilityScore
          arms eta (score t) (prob t) (loss t) (next t)
          (history t omega, action t omega))) := by
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range horizon) _ (fun t _ => hscoreComp t)
    _ <= (Finset.range horizon).sum (fun t => integral mu (fun omega =>
        refinedPotentialStabilityBound arms eta (prob t)
          (history t omega))) := by
      exact Finset.sum_le_sum fun t _ => hround t
    _ = integral mu (fun omega => (Finset.range horizon).sum (fun t =>
        refinedPotentialStabilityBound arms eta (prob t)
          (history t omega))) := by
      symm
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range horizon) _ (fun t _ => hboundComp t)

/-- The canonical generated one-round potential score on a visible
environment/prefix and sampled successor action. -/
noncomputable def sampledHalfTsallisHistoryActionPotentialStabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat) :
    (Env × History.FinitePairHistory Action Real n) × Action -> Real :=
  importanceWeightedPotentialStabilityScore arms eta
    (sampledHalfTsallisScoreAt arms harms eta n)
    (sampledHalfTsallisProbabilityAt arms harms eta n)
    (sampledHalfTsallisPredictableLossAt loss n)
    (sampledHalfTsallisUpdatedAt arms harms eta loss n)

/-- The generated visible-prefix refined potential budget. -/
noncomputable def sampledHalfTsallisRefinedPotentialStabilityBoundAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real) (n : Nat) :
    Env × History.FinitePairHistory Action Real n -> Real :=
  refinedPotentialStabilityBound arms eta
    (sampledHalfTsallisProbabilityAt arms harms eta n)

/-- The generated canonical potential score is measurable. -/
theorem measurable_sampledHalfTsallisHistoryActionPotentialStabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat) :
    Measurable (sampledHalfTsallisHistoryActionPotentialStabilityAt
      arms harms eta loss n) := by
  let selector :=
    canonicalHalfTsallisGeneratedSelectorMeasurability
      arms harms eta loss
  unfold sampledHalfTsallisHistoryActionPotentialStabilityAt
  apply measurable_importanceWeightedPotentialStabilityScore
  · intro candidate hcandidate
    exact (measurable_sampledHalfTsallisHistoryScore
      arms harms eta selector.finiteHistory n candidate hcandidate).comp
        measurable_snd
  · intro candidate hcandidate
    exact (sampledHalfTsallisEnvironmentHistoryDistributionSource
      (Env := Env) arms harms eta selector.finiteHistory n).measurable_prob
        candidate hcandidate
  · intro candidate _hcandidate
    exact measurable_sampledHalfTsallisPredictableLossAt loss n candidate
  · intro candidate hcandidate
    exact selector.measurable_updated n candidate hcandidate

/-- The generated refined potential budget is automatically integrable. -/
theorem integrable_sampledHalfTsallisRefinedPotentialStabilityBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (n : Nat)
    (historyMu : Measure
      (Env × History.FinitePairHistory Action Real n))
    [IsFiniteMeasure historyMu]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (heta : 0 < eta)
    (selector : HalfTsallisFiniteHistorySelectorMeasurability
      arms harms eta) :
    Integrable
      (sampledHalfTsallisRefinedPotentialStabilityBoundAt
        (Env := Env) arms harms eta n)
      historyMu := by
  unfold sampledHalfTsallisRefinedPotentialStabilityBoundAt
  exact integrable_refinedPotentialStabilityBound_of_finiteSimplex
    historyMu arms eta
      (sampledHalfTsallisProbabilityAt (Env := Env)
        arms harms eta n)
      (sampledHalfTsallisEnvironmentHistoryDistributionSource
        (Env := Env) arms harms eta selector n)
      heta

/-- The generated canonical potential score is automatically integrable under
the visible-history/action product law. -/
theorem integrable_sampledHalfTsallisHistoryActionPotentialStabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (heta : 0 < eta) (heta_le : eta <= 1 / 2)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat) :
    let selector :=
      canonicalHalfTsallisGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    Integrable
      (sampledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
      (mu.map (sampledHalfTsallisHistoryAt n) ⊗ₘ
        sampledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hfinite :=
    integrable_importanceWeightedPotentialStabilityScore_finiteActionKernel
      (mu.map (sampledHalfTsallisHistoryAt n))
      arms eta
      (sampledHalfTsallisScoreAt arms harms eta n)
      (sampledHalfTsallisProbabilityAt (Env := Env)
        arms harms eta n)
      (sampledHalfTsallisPredictableLossAt loss n)
      (sampledHalfTsallisUpdatedAt arms harms eta loss n)
      (sampledHalfTsallisEnvironmentHistoryDistributionSource
        (Env := Env) arms harms eta selector.finiteHistory n)
      heta heta_le
      (fun input => halfTsallisMinimizer_isRegularizedMinimizer
        arms harms eta (sampledHalfTsallisScoreAt arms harms eta n input))
      (fun input chosen _ =>
        halfTsallisUpdatedMinimizer_isRegularizedMinimizer
          arms harms eta
          (sampledHalfTsallisScoreAt arms harms eta n input)
          (sampledHalfTsallisPredictableLossAt loss n input) chosen)
      (fun input candidate _ =>
        loss.successor_mem_unitInterval n input.1 input.2 candidate)
      (measurable_sampledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
  rw [sampledHalfTsallisPolicyAt_eq_finiteActionKernel
    arms harms eta selector.finiteHistory n]
  simpa [sampledHalfTsallisHistoryActionPotentialStabilityAt, mu, selector]
    using hfinite

/-- The actual generated successor potential step, written with the next
prefix's current selector. -/
noncomputable def sampledHalfTsallisSuccessorPotentialStabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Real)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  let history := sampledHalfTsallisHistoryAt n sample
  let probability := sampledHalfTsallisProbabilityAt
    arms harms eta n history
  let estimate := Exp3.importanceWeightedLoss probability
    (sampledHalfTsallisPredictableLossAt loss n history)
    (sampledHalfTsallisActionAt n sample)
  halfTsallisPotentialStability arms eta
    (sampledHalfTsallisScoreAt arms harms eta n history)
    probability estimate
    (sampledHalfTsallisHistoryDistribution arms harms eta (n + 1)
      (Preorder.frestrictLe (n + 1) sample.2))

/--
Generated canonical finite-horizon successor conjugate-potential stability.

The trajectory action law, score recursion, selector measurability, score
integrability, and refined-budget integrability are all discharged internally.
-/
theorem integral_sum_sampledHalfTsallisSuccessorPotentialStability_le_integral_sum_refinedPotentialStabilityBound_canonical
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (horizon : Nat) (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Real) (heta : 0 < eta) (heta_le : eta <= 1 / 2)
    (loss : Exp3.PredictableLossVector Env Action) :
    let selector :=
      canonicalHalfTsallisGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledHalfTsallisSuccessorPotentialStabilityAt
          arms harms eta loss n sample)) <=
      integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta n
          (sampledHalfTsallisHistoryAt n sample))) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hhistory (n : Nat) : Measurable
      (sampledHalfTsallisHistoryAt (Env := Env) (Action := Action) n) :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have haction (n : Nat) : Measurable
      (sampledHalfTsallisActionAt (Env := Env) (Action := Action) n) :=
    measurable_fst.comp
      ((measurable_pi_apply (n + 1)).comp measurable_snd)
  have hpolicyEq (n : Nat) :
      sampledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n =
        Exp3.finiteActionKernel arms
          (sampledHalfTsallisProbabilityAt (Env := Env)
            arms harms eta n)
          (sampledHalfTsallisEnvironmentHistoryDistributionSource
            (Env := Env) arms harms eta selector.finiteHistory n) :=
    sampledHalfTsallisPolicyAt_eq_finiteActionKernel
      arms harms eta selector.finiteHistory n
  have hpolicy (n : Nat) :
      sampledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n =ᵐ[
        mu.map (sampledHalfTsallisHistoryAt n)]
        fun input => Exp3.finiteActionMeasure arms
          (sampledHalfTsallisProbabilityAt (Env := Env)
            arms harms eta n input) := by
    filter_upwards [] with input
    rw [hpolicyEq n, Exp3.finiteActionKernel_apply]
  have hcond (n : Nat) :
      condDistrib
          (sampledHalfTsallisActionAt (Env := Env) (Action := Action) n)
          (sampledHalfTsallisHistoryAt n) mu =ᵐ[
        mu.map (sampledHalfTsallisHistoryAt n)]
        sampledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n := by
    simpa [mu, sampledHalfTsallisHistoryAt, sampledHalfTsallisActionAt,
      sampledHalfTsallisPolicyAt] using
      (sampledHalfTsallisTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta selector.finiteHistory loss.environment n)
  have hscore (n : Nat) : Measurable
      (sampledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n) :=
    measurable_sampledHalfTsallisHistoryActionPotentialStabilityAt
      arms harms eta loss n
  have hIntegrable (n : Nat) : Integrable
      (sampledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
      (mu.map (sampledHalfTsallisHistoryAt n) ⊗ₘ
        sampledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n) := by
    simpa [mu, selector] using
      (integrable_sampledHalfTsallisHistoryActionPotentialStabilityAt
        prior arms harms eta heta heta_le loss n)
  have hboundIntegrable (n : Nat) : Integrable
      (sampledHalfTsallisRefinedPotentialStabilityBoundAt
        (Env := Env) arms harms eta n)
      (mu.map (sampledHalfTsallisHistoryAt n)) := by
    exact integrable_sampledHalfTsallisRefinedPotentialStabilityBoundAt
      n (mu.map (sampledHalfTsallisHistoryAt n))
      arms harms eta heta selector.finiteHistory
  have hscoreComp (n : Nat) : Integrable (fun sample =>
      sampledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n
        (sampledHalfTsallisHistoryAt n sample,
          sampledHalfTsallisActionAt n sample)) mu :=
    integrable_score_comp_history_action_of_condDistrib_generic
      mu (sampledHalfTsallisHistoryAt n) (hhistory n)
      (sampledHalfTsallisActionAt n) (haction n)
      (sampledHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta loss n)
      (sampledHalfTsallisPolicyAt (Env := Env)
        arms harms eta selector.finiteHistory n)
      (hcond n) (hIntegrable n)
  have hboundComp (n : Nat) : Integrable (fun sample =>
      sampledHalfTsallisRefinedPotentialStabilityBoundAt
        (Env := Env) arms harms eta n
        (sampledHalfTsallisHistoryAt n sample)) mu := by
    simpa [Function.comp_def] using
      (hboundIntegrable n).comp_measurable (hhistory n)
  have hround (n : Nat) :
      integral mu (fun sample =>
        sampledHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta loss n
          (sampledHalfTsallisHistoryAt n sample,
            sampledHalfTsallisActionAt n sample)) <=
      integral mu (fun sample =>
        sampledHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta n
          (sampledHalfTsallisHistoryAt n sample)) := by
    have h :=
      integral_importanceWeightedPotentialStabilityScore_le_integral_refinedBound_of_condDistrib_of_minimizers
        mu (sampledHalfTsallisHistoryAt n) (hhistory n)
        (sampledHalfTsallisActionAt n) (haction n)
        arms eta
        (sampledHalfTsallisScoreAt arms harms eta n)
        (sampledHalfTsallisProbabilityAt (Env := Env)
          arms harms eta n)
        (sampledHalfTsallisPredictableLossAt loss n)
        (sampledHalfTsallisUpdatedAt arms harms eta loss n)
        (sampledHalfTsallisPolicyAt (Env := Env)
          arms harms eta selector.finiteHistory n)
        (hpolicy n) (hcond n) heta heta_le
        (fun input => halfTsallisMinimizer_isRegularizedMinimizer
          arms harms eta (sampledHalfTsallisScoreAt arms harms eta n input))
        (fun input chosen _ =>
          halfTsallisUpdatedMinimizer_isRegularizedMinimizer
            arms harms eta
            (sampledHalfTsallisScoreAt arms harms eta n input)
            (sampledHalfTsallisPredictableLossAt loss n input) chosen)
        (fun input candidate _ =>
          loss.successor_mem_unitInterval n input.1 input.2 candidate)
        (hscore n) (hIntegrable n) (hboundIntegrable n)
    calc
      integral mu (fun sample =>
          sampledHalfTsallisHistoryActionPotentialStabilityAt
            arms harms eta loss n
            (sampledHalfTsallisHistoryAt n sample,
              sampledHalfTsallisActionAt n sample)) <=
        integral (mu.map (sampledHalfTsallisHistoryAt n))
          (sampledHalfTsallisRefinedPotentialStabilityBoundAt
            (Env := Env) arms harms eta n) := by
          simpa [sampledHalfTsallisHistoryActionPotentialStabilityAt,
            sampledHalfTsallisRefinedPotentialStabilityBoundAt] using h
      _ = integral mu (fun sample =>
          sampledHalfTsallisRefinedPotentialStabilityBoundAt
            (Env := Env) arms harms eta n
            (sampledHalfTsallisHistoryAt n sample)) := by
        rw [integral_map (hhistory n).aemeasurable
          (hboundIntegrable n).aestronglyMeasurable]
  have hterm (n : Nat) :
      (fun sample => sampledHalfTsallisSuccessorPotentialStabilityAt
        arms harms eta loss n sample) =ᵐ[mu]
      (fun sample =>
        sampledHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta loss n
          (sampledHalfTsallisHistoryAt n sample,
            sampledHalfTsallisActionAt n sample)) := by
    have hscoreSucc := sampledHalfTsallisScoreAt_succ_ae
      prior arms harms eta selector.finiteHistory loss n
    dsimp only at hscoreSucc
    filter_upwards [hscoreSucc] with sample hscoreSuccSample
    have hnext :
        sampledHalfTsallisHistoryDistribution arms harms eta (n + 1)
            (Preorder.frestrictLe (n + 1) sample.2) =
          sampledHalfTsallisUpdatedAt arms harms eta loss n
            (sampledHalfTsallisHistoryAt n sample)
            (sampledHalfTsallisActionAt n sample) := by
      simp only [sampledHalfTsallisHistoryDistribution,
        sampledHalfTsallisUpdatedAt, halfTsallisHistoryMinimizer,
        halfTsallisHistoryUpdatedMinimizer, halfTsallisUpdatedMinimizer,
        sampledHalfTsallisScoreAt, sampledHalfTsallisPredictableLossAt,
        sampledHalfTsallisHistoryAt, sampledHalfTsallisActionAt]
      rw [hscoreSuccSample]
      rfl
    simp only [sampledHalfTsallisSuccessorPotentialStabilityAt,
      sampledHalfTsallisHistoryActionPotentialStabilityAt,
      importanceWeightedPotentialStabilityScore]
    rw [hnext]
  have htermAll : ∀ᵐ sample ∂mu, ∀ n,
      sampledHalfTsallisSuccessorPotentialStabilityAt
          arms harms eta loss n sample =
        sampledHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta loss n
          (sampledHalfTsallisHistoryAt n sample,
            sampledHalfTsallisActionAt n sample) := by
    rw [ae_all_iff]
    exact hterm
  calc
    integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledHalfTsallisSuccessorPotentialStabilityAt
          arms harms eta loss n sample)) =
      integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta loss n
          (sampledHalfTsallisHistoryAt n sample,
            sampledHalfTsallisActionAt n sample))) := by
      apply integral_congr_ae
      filter_upwards [htermAll] with sample hsample
      exact Finset.sum_congr rfl fun n _ => hsample n
    _ = (Finset.range horizon).sum (fun n => integral mu (fun sample =>
        sampledHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta loss n
          (sampledHalfTsallisHistoryAt n sample,
            sampledHalfTsallisActionAt n sample))) := by
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range horizon) _ (fun n _ => hscoreComp n)
    _ <= (Finset.range horizon).sum (fun n => integral mu (fun sample =>
        sampledHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta n
          (sampledHalfTsallisHistoryAt n sample))) := by
      exact Finset.sum_le_sum fun n _ => hround n
    _ = integral mu (fun sample => (Finset.range horizon).sum (fun n =>
        sampledHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta n
          (sampledHalfTsallisHistoryAt n sample))) := by
      symm
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range horizon) _ (fun n _ => hboundComp n)

end Tsallis
end BanditRLProof
