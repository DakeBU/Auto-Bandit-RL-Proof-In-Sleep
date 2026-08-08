import BanditRLProof.TsallisOracleRestartExpectedStability
import BanditRLProof.TsallisConstrainedQuadraticOptimization
import BanditRLProof.TsallisRefinedSuboptimalStability
import BanditRLProof.TsallisScheduledRefinedExpectedPenalty
import BanditRLProof.TsallisSqrtScheduleSelfBoundingOptimization

/-!
# Oracle-restart refined stability tuning

This module tunes the refined half-Tsallis one-round stability certificate on
an actual contiguous oracle-restart epoch.  All expectations remain under the
single global generated restart law; the shifted trajectory is used only for
pathwise local-time indexing.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- The refined all-arm half-Tsallis budget is bounded by the square-root
mass of the arms other than any distinguished supported arm. -/
theorem refinedPotentialStabilityBound_le_two_mul_eta_mul_sqrt_erase_card
    {History : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) {best : Action} (hbest : best ∈ arms)
    (eta : Real) (heta : 0 <= eta)
    (probability : History -> Action -> Real) (history : History)
    (hprobability : FTRL.finiteSimplex arms (probability history)) :
    refinedPotentialStabilityBound arms eta probability history <=
      2 * eta * Real.sqrt ((arms.erase best).card : Real) +
        2 * eta ^ 2 := by
  have hall :=
    sum_sqrt_mul_one_sub_le_two_mul_sum_erase_sqrt
      arms hbest (probability history) hprobability
  have herase :=
    sum_erase_sqrt_le_sqrt_card
      arms hbest (probability history) hprobability
  unfold refinedPotentialStabilityBound
  calc
    eta * arms.sum (fun action =>
        Real.sqrt (probability history action) *
          (1 - probability history action)) +
        2 * eta ^ 2 <=
      eta * (2 * (arms.erase best).sum (fun action =>
        Real.sqrt (probability history action))) +
        2 * eta ^ 2 := by
          exact add_le_add (mul_le_mul_of_nonneg_left hall heta) le_rfl
    _ <= eta * (2 * Real.sqrt ((arms.erase best).card : Real)) +
        2 * eta ^ 2 := by
          have htwoEta : 0 <= 2 * eta := mul_nonneg (by norm_num) heta
          have hscaled :
              eta * (2 * (arms.erase best).sum (fun action =>
                  Real.sqrt (probability history action))) <=
                eta * (2 * Real.sqrt ((arms.erase best).card : Real)) := by
            calc
              eta * (2 * (arms.erase best).sum (fun action =>
                  Real.sqrt (probability history action))) =
                  (2 * eta) * (arms.erase best).sum (fun action =>
                    Real.sqrt (probability history action)) := by ring
              _ <= (2 * eta) *
                  Real.sqrt ((arms.erase best).card : Real) :=
                mul_le_mul_of_nonneg_left herase htwoEta
              _ = eta * (2 *
                  Real.sqrt ((arms.erase best).card : Real)) := by ring
          exact add_le_add hscaled le_rfl
    _ = 2 * eta * Real.sqrt ((arms.erase best).card : Real) +
        2 * eta ^ 2 := by ring

/-- One actual restart-local successor has the deterministic refined
square-root-cardinality budget under the single global generated law. -/
theorem
    integral_sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtSuccessor_le_two_mul_eta_mul_sqrt_erase_card
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    {best : Action} (hbest : best ∈ arms)
    (heta : 0 < eta (oracleRestartLocalTime schedule (n + 1)))
    (heta_le : eta (oracleRestartLocalTime schedule (n + 1)) <= 1 / 2) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    let term := fun sample =>
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta
        (oracleRestartShiftedTrajectory
          (schedule.start (n + 1)) sample)
        (oracleRestartLocalTime schedule (n + 1))
    Integrable term mu ∧
      integral mu term <=
        2 * eta (oracleRestartLocalTime schedule (n + 1)) *
            Real.sqrt ((arms.erase best).card : Real) +
          2 * eta (oracleRestartLocalTime schedule (n + 1)) ^ 2 := by
  dsimp only
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  let localTime := oracleRestartLocalTime schedule (n + 1)
  let term := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    sampledScheduledHalfTsallisPotentialStabilityAtTime
      arms harms eta
      (oracleRestartShiftedTrajectory (schedule.start (n + 1)) sample)
      localTime
  let history := sampledOracleRestartHalfTsallisHistoryAt
    (Env := Env) (Action := Action) n
  let bound := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    sampledOracleRestartHalfTsallisRefinedPotentialStabilityBoundAt
      (Env := Env) arms harms eta schedule n (history sample)
  let budget :=
    2 * eta localTime * Real.sqrt ((arms.erase best).card : Real) +
      2 * eta localTime ^ 2
  have hbase :=
    integral_sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtSuccessor_le_refined
      prior arms harms eta schedule loss n heta heta_le
  dsimp only at hbase
  have hboundPointwise : ∀ sample, bound sample <= budget := by
    intro sample
    have hsimplex :
        FTRL.finiteSimplex arms
          (sampledOracleRestartHalfTsallisProbabilityAt
            arms harms eta schedule n (history sample)) :=
      (sampledOracleRestartHalfTsallisProbabilityAt_isRegularizedMinimizer
        arms harms eta schedule n (history sample)).1
    simpa [bound, budget, localTime,
      sampledOracleRestartHalfTsallisRefinedPotentialStabilityBoundAt] using
      (refinedPotentialStabilityBound_le_two_mul_eta_mul_sqrt_erase_card
        arms hbest (eta localTime) heta.le
        (sampledOracleRestartHalfTsallisProbabilityAt
          (Env := Env) arms harms eta schedule n)
        (history sample) hsimplex)
  have hboundIntegrable : Integrable bound mu := by
    simpa [bound, history, mu] using hbase.2.1
  have hbudgetIntegrable :
      Integrable (fun _sample : Env × ((k : Nat) -> Action × Real) =>
        budget) mu :=
    integrable_const budget
  refine ⟨by simpa [term, localTime, mu] using hbase.1, ?_⟩
  calc
    integral mu term <= integral mu bound := by
      simpa [term, bound, history, localTime, mu] using hbase.2.2
    _ <= integral mu (fun _sample => budget) :=
      integral_mono_ae hboundIntegrable hbudgetIntegrable
        (Filter.Eventually.of_forall hboundPointwise)
    _ = budget := by simp [mu]
    _ = 2 * eta (oracleRestartLocalTime schedule (n + 1)) *
            Real.sqrt ((arms.erase best).card : Real) +
          2 * eta (oracleRestartLocalTime schedule (n + 1)) ^ 2 := rfl

theorem one_div_natSucc_le_one_div_sqrt_natSucc (t : Nat) :
    1 / (((t + 1 : Nat) : Real)) <=
      1 / Real.sqrt (((t + 1 : Nat) : Real)) := by
  let x : Real := ((t + 1 : Nat) : Real)
  have hxPos : 0 < x := by
    dsimp [x]
    positivity
  have hxOne : 1 <= x := by
    dsimp [x]
    norm_num
  have hsqrtLe : Real.sqrt x <= x := by
    calc
      Real.sqrt x <= Real.sqrt (x ^ 2) := by
        exact Real.sqrt_le_sqrt (by nlinarith)
      _ = x := Real.sqrt_sq hxPos.le
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hxPos) hsqrtLe

theorem sampledScheduledHalfTsallisSqrtSchedule_two_mul (t : Nat) :
    2 * sampledScheduledHalfTsallisSqrtSchedule t =
      1 / Real.sqrt (((t + 1 : Nat) : Real)) := by
  unfold sampledScheduledHalfTsallisSqrtSchedule
  have hcastPos : 0 < (((t + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.zero_lt_succ t
  have hsqrtNe :
      Real.sqrt (((t + 1 : Nat) : Real)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcastPos)
  field_simp [hsqrtNe]

theorem sampledScheduledHalfTsallisSqrtSchedule_two_mul_sq (t : Nat) :
    2 * sampledScheduledHalfTsallisSqrtSchedule t ^ 2 =
      (1 / 2 : Real) * (1 / (((t + 1 : Nat) : Real))) := by
  have hfour :=
    sampledScheduledHalfTsallisSqrtSchedule_four_mul_sq t
  nlinarith

theorem one_div_sampledScheduledHalfTsallisSqrtSchedule (t : Nat) :
    1 / sampledScheduledHalfTsallisSqrtSchedule t =
      2 * Real.sqrt (((t + 1 : Nat) : Real)) := by
  unfold sampledScheduledHalfTsallisSqrtSchedule
  have hcastPos : 0 < (((t + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.zero_lt_succ t
  have hsqrtNe :
      Real.sqrt (((t + 1 : Nat) : Real)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcastPos)
  field_simp [hsqrtNe]

/-- The deterministic refined budgets of the square-root schedule have an
inclusive prefix bound of order `sqrt(card * time)`. -/
theorem
    sum_range_sampledScheduledHalfTsallisSqrtSchedule_refinedBudget_le_three_mul_sqrt
    {Action : Type u}
    (arms : Finset Action) (harms : arms.Nonempty) (n : Nat) :
    (Finset.range n).sum (fun t =>
        2 * sampledScheduledHalfTsallisSqrtSchedule t *
            Real.sqrt (arms.card : Real) +
          2 * sampledScheduledHalfTsallisSqrtSchedule t ^ 2) <=
      3 * Real.sqrt (arms.card : Real) * Real.sqrt (n : Real) := by
  let sqrtCard := Real.sqrt (arms.card : Real)
  have hcardOne : 1 <= (arms.card : Real) := by
    exact_mod_cast (Finset.one_le_card.mpr harms)
  have hsqrtCardOne : 1 <= sqrtCard := by
    dsimp [sqrtCard]
    simpa using Real.sqrt_le_sqrt hcardOne
  have hsqrtCardNonneg : 0 <= sqrtCard := le_trans (by norm_num) hsqrtCardOne
  have hterm (t : Nat) :
      2 * sampledScheduledHalfTsallisSqrtSchedule t * sqrtCard +
          2 * sampledScheduledHalfTsallisSqrtSchedule t ^ 2 <=
        (3 / 2 * sqrtCard) *
          (1 / Real.sqrt (((t + 1 : Nat) : Real))) := by
    have hinvNonneg :
        0 <= 1 / Real.sqrt (((t + 1 : Nat) : Real)) := by positivity
    have hquadratic :=
      one_div_natSucc_le_one_div_sqrt_natSucc t
    have hcoefficient :
        sqrtCard + 1 / 2 <= 3 / 2 * sqrtCard := by
      nlinarith
    rw [sampledScheduledHalfTsallisSqrtSchedule_two_mul,
      sampledScheduledHalfTsallisSqrtSchedule_two_mul_sq]
    calc
      (1 / Real.sqrt (((t + 1 : Nat) : Real))) * sqrtCard +
          (1 / 2 : Real) * (1 / (((t + 1 : Nat) : Real))) <=
        (1 / Real.sqrt (((t + 1 : Nat) : Real))) * sqrtCard +
          (1 / 2 : Real) *
            (1 / Real.sqrt (((t + 1 : Nat) : Real))) := by
              exact add_le_add le_rfl
                (mul_le_mul_of_nonneg_left hquadratic (by norm_num))
      _ = (sqrtCard + 1 / 2) *
          (1 / Real.sqrt (((t + 1 : Nat) : Real))) := by ring
      _ <= (3 / 2 * sqrtCard) *
          (1 / Real.sqrt (((t + 1 : Nat) : Real))) :=
        mul_le_mul_of_nonneg_right hcoefficient hinvNonneg
  have hsumTerm :
      (Finset.range n).sum (fun t =>
          2 * sampledScheduledHalfTsallisSqrtSchedule t * sqrtCard +
            2 * sampledScheduledHalfTsallisSqrtSchedule t ^ 2) <=
        (Finset.range n).sum (fun t =>
          (3 / 2 * sqrtCard) *
            (1 / Real.sqrt (((t + 1 : Nat) : Real)))) :=
    Finset.sum_le_sum (fun t _ht => hterm t)
  have hinvSum :=
    sum_range_one_div_sqrt_natSucc_le_two_sqrt n
  calc
    (Finset.range n).sum (fun t =>
        2 * sampledScheduledHalfTsallisSqrtSchedule t *
            Real.sqrt (arms.card : Real) +
          2 * sampledScheduledHalfTsallisSqrtSchedule t ^ 2) <=
      (Finset.range n).sum (fun t =>
        (3 / 2 * sqrtCard) *
          (1 / Real.sqrt (((t + 1 : Nat) : Real)))) := by
            simpa [sqrtCard] using hsumTerm
    _ = (3 / 2 * sqrtCard) *
        (Finset.range n).sum (fun t =>
          1 / Real.sqrt (((t + 1 : Nat) : Real))) := by
            rw [Finset.mul_sum]
    _ <= (3 / 2 * sqrtCard) * (2 * Real.sqrt (n : Real)) :=
      mul_le_mul_of_nonneg_left hinvSum (by positivity)
    _ = 3 * Real.sqrt (arms.card : Real) * Real.sqrt (n : Real) := by
      dsimp [sqrtCard]
      ring

/-- A deterministic contiguous restart epoch has an expected shifted
stability prefix bounded by `4 * sqrt(K) * sqrt(epoch length)`. -/
theorem
    integral_sum_sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtLocalPrefix_sqrtSchedule_le_four_mul_sqrt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epoch localHorizon : Nat)
    {best : Action} (hbest : best ∈ arms)
    (hstart : ∀ localTime, localTime <= localHorizon ->
      schedule.start (epoch + localTime) = epoch) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms sampledScheduledHalfTsallisSqrtSchedule schedule
        loss.environment
    let stabilitySum := fun sample =>
      (Finset.range (localHorizon + 1)).sum (fun localTime =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms sampledScheduledHalfTsallisSqrtSchedule
          (oracleRestartShiftedTrajectory epoch sample) localTime)
    Integrable stabilitySum mu ∧
      integral mu stabilitySum <=
        4 * Real.sqrt (arms.card : Real) *
          Real.sqrt ((localHorizon + 1 : Nat) : Real) := by
  dsimp only
  let eta := sampledScheduledHalfTsallisSqrtSchedule
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  let term := fun localTime
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    sampledScheduledHalfTsallisPotentialStabilityAtTime
      arms harms eta (oracleRestartShiftedTrajectory epoch sample) localTime
  let budget := fun localTime =>
    2 * eta localTime * Real.sqrt (arms.card : Real) +
      2 * eta localTime ^ 2
  have hstartZero : schedule.start epoch = epoch := by
    simpa using hstart 0 (Nat.zero_le localHorizon)
  have hlocalZero :
      oracleRestartLocalTime schedule epoch = 0 := by
    simp [oracleRestartLocalTime, hstartZero]
  have hzero :
      Integrable (term 0) mu ∧ integral mu (term 0) <= 1 := by
    have hround :=
      integral_sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtTime_le_integral_one
        prior arms harms eta schedule loss epoch
          (by
            simpa [hlocalZero, eta] using
              sampledScheduledHalfTsallisSqrtSchedule_pos 0)
    dsimp only at hround
    have hmass : integral mu (fun _sample => (1 : Real)) = 1 := by
      simp [mu]
    refine ⟨by
      simpa [term, eta, mu, hstartZero, hlocalZero] using hround.1, ?_⟩
    calc
      integral mu (term 0) <= integral mu (fun _sample => (1 : Real)) := by
        simpa [term, eta, mu, hstartZero, hlocalZero] using hround.2
      _ = 1 := hmass
  have hsucc (localTime : Nat) (hlocalTime : 0 < localTime)
      (hle : localTime <= localHorizon) :
      Integrable (term localTime) mu ∧
        integral mu (term localTime) <= budget localTime := by
    obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hlocalTime)
    have hlocal :
        oracleRestartLocalTime schedule (epoch + (predecessor + 1)) =
          predecessor + 1 := by
      simp [oracleRestartLocalTime, hstart (predecessor + 1) hle]
    have hactualLocal :
        oracleRestartLocalTime schedule (epoch + predecessor + 1) =
          predecessor + 1 := by
      simpa [Nat.add_assoc] using hlocal
    have hround :=
      integral_sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtSuccessor_le_two_mul_eta_mul_sqrt_erase_card
        prior arms harms eta schedule loss (epoch + predecessor) hbest
        (by
          simpa [hactualLocal, eta] using
            sampledScheduledHalfTsallisSqrtSchedule_pos (predecessor + 1))
        (by
          simpa [hactualLocal, eta] using
            sampledScheduledHalfTsallisSqrtSchedule_le_half (predecessor + 1))
    dsimp only at hround
    have hcardReal :
        (((arms.erase best).card : Nat) : Real) <= (arms.card : Real) := by
      exact_mod_cast
        (Finset.card_erase_le : (arms.erase best).card <= arms.card)
    have hsqrtCard :
        Real.sqrt ((arms.erase best).card : Real) <=
          Real.sqrt (arms.card : Real) :=
      Real.sqrt_le_sqrt hcardReal
    have hscale :
        0 <= 2 * eta (predecessor + 1) := by
      exact mul_nonneg (by norm_num)
        (sampledScheduledHalfTsallisSqrtSchedule_pos _).le
    refine ⟨by
      simpa [term, eta, mu, hstart (predecessor + 1) hle, hlocal,
        Nat.add_assoc] using hround.1, ?_⟩
    calc
      integral mu (term (predecessor + 1)) <=
          2 * eta (predecessor + 1) *
              Real.sqrt ((arms.erase best).card : Real) +
            2 * eta (predecessor + 1) ^ 2 := by
        simpa [term, eta, mu, hstart (predecessor + 1) hle, hlocal,
          Nat.add_assoc] using hround.2
      _ <= 2 * eta (predecessor + 1) *
              Real.sqrt (arms.card : Real) +
            2 * eta (predecessor + 1) ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsqrtCard hscale) le_rfl
      _ = budget (predecessor + 1) := rfl
  have hterm (localTime : Nat)
      (hmem : localTime ∈ Finset.range (localHorizon + 1)) :
      Integrable (term localTime) mu := by
    by_cases hlocalTime : localTime = 0
    · simpa [hlocalTime] using hzero.1
    · exact (hsucc localTime (Nat.pos_of_ne_zero hlocalTime)
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem))).1
  have hsumIntegrable :
      Integrable (fun sample =>
        (Finset.range (localHorizon + 1)).sum
          (fun localTime => term localTime sample)) mu :=
    IntegrabilitySums.integrable_finset_sum mu
      (Finset.range (localHorizon + 1)) term hterm
  have hintegralSum :
      integral mu (fun sample =>
        (Finset.range (localHorizon + 1)).sum
          (fun localTime => term localTime sample)) =
        (Finset.range (localHorizon + 1)).sum
          (fun localTime => integral mu (term localTime)) :=
    ExpectationBochnerSums.integral_finset_sum mu
      (Finset.range (localHorizon + 1)) term hterm
  have hsuccessorSum :
      (Finset.range localHorizon).sum (fun predecessor =>
          integral mu (term (predecessor + 1))) <=
        (Finset.range localHorizon).sum (fun predecessor =>
          budget (predecessor + 1)) := by
    apply Finset.sum_le_sum
    intro predecessor hpredecessor
    exact (hsucc (predecessor + 1) (by omega)
      (Nat.succ_le_iff.mpr (Finset.mem_range.mp hpredecessor))).2
  have hbudgetZero : 0 <= budget 0 := by
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (sampledScheduledHalfTsallisSqrtSchedule_pos 0).le)
        (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have hsuccessorToFull :
      (Finset.range localHorizon).sum (fun predecessor =>
          budget (predecessor + 1)) <=
        (Finset.range (localHorizon + 1)).sum budget := by
    rw [Finset.sum_range_succ']
    exact le_add_of_nonneg_right hbudgetZero
  have hbudgetSum :=
    sum_range_sampledScheduledHalfTsallisSqrtSchedule_refinedBudget_le_three_mul_sqrt
      arms harms (localHorizon + 1)
  have hsqrtCardOne : 1 <= Real.sqrt (arms.card : Real) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt
      (show (1 : Real) <= (arms.card : Real) by
        exact_mod_cast Finset.one_le_card.mpr harms)
  have hsqrtTimeOne :
      1 <= Real.sqrt ((localHorizon + 1 : Nat) : Real) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le localHorizon)
  refine ⟨by simpa [term, eta, mu] using hsumIntegrable, ?_⟩
  calc
    integral mu (fun sample =>
        (Finset.range (localHorizon + 1)).sum
          (fun localTime => term localTime sample)) =
      integral mu (term 0) +
        (Finset.range localHorizon).sum (fun predecessor =>
          integral mu (term (predecessor + 1))) := by
            rw [hintegralSum, Finset.sum_range_succ']
            exact add_comm _ _
    _ <= 1 + (Finset.range localHorizon).sum (fun predecessor =>
          budget (predecessor + 1)) :=
      add_le_add hzero.2 hsuccessorSum
    _ <= 1 + (Finset.range (localHorizon + 1)).sum budget :=
      add_le_add le_rfl hsuccessorToFull
    _ <= 1 + 3 * Real.sqrt (arms.card : Real) *
          Real.sqrt ((localHorizon + 1 : Nat) : Real) := by
      simpa [budget, eta] using add_le_add_left hbudgetSum 1
    _ <= 4 * Real.sqrt (arms.card : Real) *
          Real.sqrt ((localHorizon + 1 : Nat) : Real) := by
      have hproduct :
          1 <= Real.sqrt (arms.card : Real) *
            Real.sqrt ((localHorizon + 1 : Nat) : Real) :=
        by
          simpa only [one_mul] using
            (mul_le_mul hsqrtCardOne hsqrtTimeOne
              (by norm_num : (0 : Real) <= 1)
              (Real.sqrt_nonneg _))
      nlinarith

/-- The terminal point-mass penalty of one square-root-scheduled epoch is
bounded by `4 * sqrt(K) * sqrt(epoch length)`. -/
theorem
    initialHalfTsallisPotentialMass_sqrtSchedule_pointMassPenalty_le_four_mul_sqrt
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    {best : Action} (hbest : best ∈ arms) (localHorizon : Nat) :
    halfTsallisPotentialMass arms
          (initialHalfTsallisDistribution arms harms
            (sampledScheduledHalfTsallisSqrtSchedule 0)) /
        sampledScheduledHalfTsallisSqrtSchedule localHorizon -
      1 / sampledScheduledHalfTsallisSqrtSchedule localHorizon <=
        4 * Real.sqrt (arms.card : Real) *
          Real.sqrt ((localHorizon + 1 : Nat) : Real) := by
  let probability :=
    initialHalfTsallisDistribution arms harms
      (sampledScheduledHalfTsallisSqrtSchedule 0)
  have hdistribution :=
    finiteActionDistribution_initialHalfTsallisDistribution
      arms harms (sampledScheduledHalfTsallisSqrtSchedule 0)
  have hsimplex : FTRL.finiteSimplex arms probability :=
    ⟨hdistribution.nonneg, hdistribution.sum_eq_one⟩
  have hmassRefined :=
    halfTsallisPotentialMass_sub_one_le_two_mul_sum_erase_refined
      arms hbest probability hsimplex
  have hrefinedLe :
      (arms.erase best).sum (fun action =>
          Real.sqrt (probability action) - probability action / 2) <=
        (arms.erase best).sum (fun action =>
          Real.sqrt (probability action)) := by
    apply Finset.sum_le_sum
    intro action haction
    have hnonneg :=
      hsimplex.1 action (Finset.mem_of_mem_erase haction)
    linarith
  have herase :=
    sum_erase_sqrt_le_sqrt_card arms hbest probability hsimplex
  have hcardReal :
      (((arms.erase best).card : Nat) : Real) <= (arms.card : Real) := by
    exact_mod_cast
      (Finset.card_erase_le : (arms.erase best).card <= arms.card)
  have hsqrtCard :
      Real.sqrt ((arms.erase best).card : Real) <=
        Real.sqrt (arms.card : Real) :=
    Real.sqrt_le_sqrt hcardReal
  have hmass :
      halfTsallisPotentialMass arms probability - 1 <=
        2 * Real.sqrt (arms.card : Real) := by
    calc
      halfTsallisPotentialMass arms probability - 1 <=
          2 * (arms.erase best).sum (fun action =>
            Real.sqrt (probability action) - probability action / 2) :=
        hmassRefined
      _ <= 2 * (arms.erase best).sum (fun action =>
            Real.sqrt (probability action)) :=
        mul_le_mul_of_nonneg_left hrefinedLe (by norm_num)
      _ <= 2 * Real.sqrt ((arms.erase best).card : Real) :=
        mul_le_mul_of_nonneg_left herase (by norm_num)
      _ <= 2 * Real.sqrt (arms.card : Real) :=
        mul_le_mul_of_nonneg_left hsqrtCard (by norm_num)
  have hetaPos :
      0 < sampledScheduledHalfTsallisSqrtSchedule localHorizon :=
    sampledScheduledHalfTsallisSqrtSchedule_pos localHorizon
  calc
    halfTsallisPotentialMass arms
          (initialHalfTsallisDistribution arms harms
            (sampledScheduledHalfTsallisSqrtSchedule 0)) /
        sampledScheduledHalfTsallisSqrtSchedule localHorizon -
      1 / sampledScheduledHalfTsallisSqrtSchedule localHorizon =
        (halfTsallisPotentialMass arms probability - 1) *
          (1 / sampledScheduledHalfTsallisSqrtSchedule localHorizon) := by
            dsimp [probability]
            ring
    _ <= 2 * Real.sqrt (arms.card : Real) *
          (1 / sampledScheduledHalfTsallisSqrtSchedule localHorizon) :=
      mul_le_mul_of_nonneg_right hmass (one_div_nonneg.mpr hetaPos.le)
    _ = 4 * Real.sqrt (arms.card : Real) *
          Real.sqrt ((localHorizon + 1 : Nat) : Real) := by
      rw [one_div_sampledScheduledHalfTsallisSqrtSchedule]
      ring

/-- An actual contiguous restart epoch run with the square-root schedule has
the `C * sqrt(epoch length)` observed estimated-regret certificate required
by the restart dynamic-regret assembly, with `C = 8 * sqrt(K)`. -/
theorem
    integral_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_sqrtSchedule_le_eight_mul_sqrt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (horizon epoch localHorizon : Nat)
    {best : Action} (hbest : best ∈ arms)
    (hRounds :
      oracleRestartEpochRounds schedule.start horizon epoch =
        (Finset.range (localHorizon + 1)).image
          (fun localTime => epoch + localTime)) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms sampledScheduledHalfTsallisSqrtSchedule schedule
        loss.environment
    let observed :=
      sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
        (Env := Env) arms harms sampledScheduledHalfTsallisSqrtSchedule
          schedule (pointMass best) horizon epoch
    Integrable observed mu ∧
      integral mu observed <=
        (8 * Real.sqrt (arms.card : Real)) *
          Real.sqrt ((localHorizon + 1 : Nat) : Real) := by
  dsimp only
  let eta := sampledScheduledHalfTsallisSqrtSchedule
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  let observed :=
    sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
      (Env := Env) arms harms eta schedule (pointMass best) horizon epoch
  let stabilitySum := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    (Finset.range (localHorizon + 1)).sum (fun localTime =>
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta
        (oracleRestartShiftedTrajectory epoch sample) localTime)
  let penalty :=
    halfTsallisPotentialMass arms
        (initialHalfTsallisDistribution arms harms (eta 0)) /
      eta localHorizon -
    1 / eta localHorizon
  let rhs := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    stabilitySum sample + penalty
  have hstart (localTime : Nat) (hle : localTime <= localHorizon) :
      schedule.start (epoch + localTime) = epoch := by
    have hmemRange :
        localTime ∈ Finset.range (localHorizon + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hle)
    have hmemImage :
        epoch + localTime ∈
          (Finset.range (localHorizon + 1)).image
            (fun localTime => epoch + localTime) :=
      Finset.mem_image.mpr ⟨localTime, hmemRange, rfl⟩
    have hmemRounds :
        epoch + localTime ∈
          oracleRestartEpochRounds schedule.start horizon epoch := by
      rw [hRounds]
      exact hmemImage
    exact (Finset.mem_filter.mp hmemRounds).2
  have hstability :=
    integral_sum_sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtLocalPrefix_sqrtSchedule_le_four_mul_sqrt
      prior arms harms schedule loss epoch localHorizon hbest hstart
  dsimp only at hstability
  have hstabilityIntegrable : Integrable stabilitySum mu := by
    simpa [stabilitySum, eta, mu] using hstability.1
  have hstabilityBound :
      integral mu stabilitySum <=
        4 * Real.sqrt (arms.card : Real) *
          Real.sqrt ((localHorizon + 1 : Nat) : Real) := by
    simpa [stabilitySum, eta, mu] using hstability.2
  have hpenalty :
      penalty <=
        4 * Real.sqrt (arms.card : Real) *
          Real.sqrt ((localHorizon + 1 : Nat) : Real) := by
    simpa [penalty, eta] using
      (initialHalfTsallisPotentialMass_sqrtSchedule_pointMassPenalty_le_four_mul_sqrt
        arms harms hbest localHorizon)
  have hobservedData :=
    integral_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_eq_epochRegret
      prior arms harms eta schedule loss (fun _epoch => best) epoch hbest
      horizon
  dsimp only at hobservedData
  have hobserved : Integrable observed mu := by
    simpa [observed, mu] using hobservedData.1
  have hrhsIntegrable : Integrable rhs mu :=
    hstabilityIntegrable.add (integrable_const _)
  have hpathwise : ∀ᵐ sample ∂mu, observed sample <= rhs sample := by
    filter_upwards [] with sample
    have hbase :=
      sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_le_stability_add_penalty_of_epochRounds_eq
        arms harms eta schedule horizon epoch localHorizon sample hbest
        hRounds
        (fun localTime _hle =>
          sampledScheduledHalfTsallisSqrtSchedule_pos localTime)
        (fun localTime _hlt =>
          sampledScheduledHalfTsallisSqrtSchedule_succ_le localTime)
    unfold observed rhs stabilitySum penalty
    simp only [sampledScheduledHalfTsallisProbabilityAtTime] at hbase
    linarith
  have hintegrated :=
    integral_mono_ae hobserved hrhsIntegrable hpathwise
  have hrhsIntegral :
      integral mu rhs = integral mu stabilitySum + penalty := by
    unfold rhs
    rw [integral_add hstabilityIntegrable (integrable_const _)]
    simp
  refine ⟨hobserved, ?_⟩
  calc
    integral mu observed <= integral mu rhs := hintegrated
    _ = integral mu stabilitySum + penalty := hrhsIntegral
    _ <=
        4 * Real.sqrt (arms.card : Real) *
            Real.sqrt ((localHorizon + 1 : Nat) : Real) +
          4 * Real.sqrt (arms.card : Real) *
            Real.sqrt ((localHorizon + 1 : Nat) : Real) :=
      add_le_add hstabilityBound hpenalty
    _ = (8 * Real.sqrt (arms.card : Real)) *
          Real.sqrt ((localHorizon + 1 : Nat) : Real) := by ring

/-- Cardinality-shaped form of the tuned epoch certificate. -/
theorem
    integral_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_sqrtSchedule_le_eight_mul_sqrt_card
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (horizon epoch localHorizon : Nat)
    {best : Action} (hbest : best ∈ arms)
    (hRounds :
      oracleRestartEpochRounds schedule.start horizon epoch =
        (Finset.range (localHorizon + 1)).image
          (fun localTime => epoch + localTime)) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms sampledScheduledHalfTsallisSqrtSchedule schedule
        loss.environment
    let observed :=
      sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
        (Env := Env) arms harms sampledScheduledHalfTsallisSqrtSchedule
          schedule (pointMass best) horizon epoch
    Integrable observed mu ∧
      integral mu observed <=
        (8 * Real.sqrt (arms.card : Real)) *
          Real.sqrt
            ((oracleRestartEpochRounds
              schedule.start horizon epoch).card : Real) := by
  have hcard :
      (oracleRestartEpochRounds schedule.start horizon epoch).card =
        localHorizon + 1 := by
    rw [hRounds, Finset.card_image_of_injective]
    · simp
    · intro localTime₁ localTime₂ heq
      exact Nat.add_left_cancel heq
  simpa [hcard] using
    (integral_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_sqrtSchedule_le_eight_mul_sqrt
      prior arms harms schedule loss horizon epoch localHorizon hbest hRounds)

/-- Every actual epoch of the restart schedule exposes the cardinality-shaped
certificate directly, with no caller-supplied local-horizon witness. -/
theorem
    integral_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_sqrtSchedule_le_eight_mul_sqrt_card_of_mem
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (horizon epoch : Nat)
    {best : Action} (hbest : best ∈ arms)
    (hepoch : epoch ∈ oracleRestartScheduleEpochs schedule horizon) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms sampledScheduledHalfTsallisSqrtSchedule schedule
        loss.environment
    let observed :=
      sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
        (Env := Env) arms harms sampledScheduledHalfTsallisSqrtSchedule
          schedule (pointMass best) horizon epoch
    Integrable observed mu ∧
      integral mu observed <=
        (8 * Real.sqrt (arms.card : Real)) *
          Real.sqrt
            ((oracleRestartEpochRounds
              schedule.start horizon epoch).card : Real) := by
  obtain ⟨localHorizon, hRounds⟩ :=
    exists_oracleRestartEpochRounds_eq_image_range
      schedule horizon epoch hepoch
  exact
    integral_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_sqrtSchedule_le_eight_mul_sqrt_card
      prior arms harms schedule loss horizon epoch localHorizon hbest hRounds

end Tsallis
end BanditRLProof
