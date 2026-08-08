import BanditRLProof.TsallisScheduledRecursiveTrajectory
import BanditRLProof.TsallisTimeVaryingPenalty

/-!
# Scheduled half-Tsallis score alignment

This module identifies the recursively accumulated scheduled half-Tsallis
history score with `FTRL.cumulativeLoss` of the actual observed
importance-weighted loss vectors.  It then rewrites the deterministic
time-varying penalty theorem onto one generated trajectory sample.

The result is pathwise.  It does not yet integrate the penalty, prove the
roundwise refined stability bound under a schedule, handle early large rates,
or conclude Tsallis-INF regret.
-/

namespace BanditRLProof
namespace Tsallis

universe u v

/-- The pure scheduled half-Tsallis sampling probability at an actual time. -/
noncomputable def sampledScheduledHalfTsallisProbabilityAtTime
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real) :
    Nat -> Env × ((k : Nat) -> Action × Real) -> Action -> Real
  | 0, _sample => initialHalfTsallisDistribution arms harms (eta 0)
  | n + 1, sample =>
      sampledScheduledHalfTsallisHistoryDistribution arms harms eta n
        (Preorder.frestrictLe n sample.2)

/-- The actual observed-scalar IW loss vector under the scheduled policy. -/
noncomputable def sampledScheduledHalfTsallisObservedEstimatedLossAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (t : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    Action -> Real :=
  Exp3.importanceWeightedLoss
    (sampledScheduledHalfTsallisProbabilityAtTime arms harms eta t sample)
    (fun _ => (sample.2 t).2) (sample.2 t).1

/-- The cumulative observed IW loss through time `n` is exactly the inclusive
scheduled finite-history score at level `n`. -/
theorem cumulativeLoss_sampledScheduledHalfTsallisObservedEstimatedLossAt_succ
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (sample : Env × ((k : Nat) -> Action × Real)) (n : Nat) :
    FTRL.cumulativeLoss
        (fun t => sampledScheduledHalfTsallisObservedEstimatedLossAt
          arms harms eta t sample) (n + 1) =
      sampledScheduledHalfTsallisHistoryScore arms harms eta n
        (Preorder.frestrictLe n sample.2) := by
  induction n with
  | zero =>
      funext action
      simp [FTRL.cumulativeLoss_succ,
        sampledScheduledHalfTsallisObservedEstimatedLossAt,
        sampledScheduledHalfTsallisProbabilityAtTime]
  | succ n ih =>
      rw [FTRL.cumulativeLoss_succ]
      funext candidate
      change
        FTRL.cumulativeLoss
              (fun t => sampledScheduledHalfTsallisObservedEstimatedLossAt
                arms harms eta t sample) (n + 1) candidate +
            sampledScheduledHalfTsallisObservedEstimatedLossAt
              arms harms eta (n + 1) sample candidate = _
      rw [ih, sampledScheduledHalfTsallisHistoryScore_succ,
        Exp3.previousPairHistory_frestrictLe]
      rfl

/-- The canonical scheduled cumulative selector is the actual generated
sampling probability at the same time. -/
@[simp]
theorem halfTsallisScheduledMinimizer_observedEstimatedLoss_eq_probabilityAtTime
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (sample : Env × ((k : Nat) -> Action × Real)) (t : Nat) :
    halfTsallisScheduledMinimizer arms harms eta
        (fun s => sampledScheduledHalfTsallisObservedEstimatedLossAt
          arms harms eta s sample) t =
      sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample := by
  cases t with
  | zero =>
      unfold halfTsallisScheduledMinimizer
        sampledScheduledHalfTsallisProbabilityAtTime
        initialHalfTsallisDistribution
      apply congrArg (halfTsallisMinimizer arms harms (eta 0))
      funext action
      simp [FTRL.cumulativeLoss]
  | succ n =>
      unfold halfTsallisScheduledMinimizer
      rw [cumulativeLoss_sampledScheduledHalfTsallisObservedEstimatedLossAt_succ]
      rfl

/-- The same-rate auxiliary minimizer after appending the actual observed IW
loss at time `t`. -/
noncomputable def sampledScheduledHalfTsallisSameRateNextAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (sample : Env × ((k : Nat) -> Action × Real)) (t : Nat) :
    Action -> Real :=
  halfTsallisScheduledSameRateNext arms harms eta
    (fun s => sampledScheduledHalfTsallisObservedEstimatedLossAt
      arms harms eta s sample) t

/-- The same-rate conjugate-potential stability term at an actual trajectory
time. -/
noncomputable def sampledScheduledHalfTsallisPotentialStabilityAtTime
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (sample : Env × ((k : Nat) -> Action × Real)) (t : Nat) : Real :=
  let observedLoss := fun s =>
    sampledScheduledHalfTsallisObservedEstimatedLossAt
      arms harms eta s sample
  halfTsallisPotentialStability arms (eta t)
    (FTRL.cumulativeLoss observedLoss t)
    (sampledScheduledHalfTsallisProbabilityAtTime
      arms harms eta t sample)
    (observedLoss t)
    (sampledScheduledHalfTsallisSameRateNextAt
      arms harms eta sample t)

/-- The scheduled potential-change penalty at an actual trajectory time. -/
noncomputable def sampledScheduledHalfTsallisPotentialPenaltyAtTime
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (q : Action -> Real)
    (sample : Env × ((k : Nat) -> Action × Real)) (t : Nat) : Real :=
  let observedLoss := fun s =>
    sampledScheduledHalfTsallisObservedEstimatedLossAt
      arms harms eta s sample
  halfTsallisPotentialValue arms (eta t)
      (FTRL.cumulativeLoss observedLoss t)
      (sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample) -
    halfTsallisPotentialValue arms (eta t)
      (FTRL.cumulativeLoss observedLoss (t + 1))
      (sampledScheduledHalfTsallisSameRateNextAt
        arms harms eta sample t) -
    FTRL.linearLoss arms q (observedLoss t)

/-- Pathwise estimated regret against a finite-simplex comparator through the
inclusive terminal time `n`. -/
noncomputable def sampledScheduledHalfTsallisEstimatedRegret
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (q : Action -> Real) (n : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (Finset.range (n + 1)).sum (fun t =>
    FTRL.linearLoss arms
        (sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample)
        (sampledScheduledHalfTsallisObservedEstimatedLossAt
          arms harms eta t sample) -
      FTRL.linearLoss arms q
        (sampledScheduledHalfTsallisObservedEstimatedLossAt
          arms harms eta t sample))

/-- Exact pathwise decomposition of generated scheduled estimated regret into
same-rate potential stability plus the learning-rate-change penalty. -/
theorem sampledScheduledHalfTsallisEstimatedRegret_eq_stability_add_penalty
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (q : Action -> Real) (n : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledScheduledHalfTsallisEstimatedRegret
        arms harms eta q n sample =
      (Finset.range (n + 1)).sum (fun t =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample t) +
      (Finset.range (n + 1)).sum (fun t =>
        sampledScheduledHalfTsallisPotentialPenaltyAtTime
          arms harms eta q sample t) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  unfold sampledScheduledHalfTsallisPotentialStabilityAtTime
    sampledScheduledHalfTsallisPotentialPenaltyAtTime
    halfTsallisPotentialStability
  dsimp only
  rw [FTRL.cumulativeLoss_succ]
  ring

/-- Pathwise generated-trajectory specialization of the scheduled point-mass
penalty theorem, retaining the explicit terminal `-1 / eta n` contribution. -/
theorem sum_sampledScheduledHalfTsallisPotentialPenalty_pointMass_le
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real)
    (sample : Env × ((k : Nat) -> Action × Real))
    {best : Action} (hbest : best ∈ arms) (n : Nat)
    (heta : forall t, t <= n -> 0 < eta t)
    (hetaMono : forall t, t < n -> eta (t + 1) <= eta t) :
    (Finset.range (n + 1)).sum (fun t =>
        sampledScheduledHalfTsallisPotentialPenaltyAtTime
          arms harms eta (pointMass best) sample t) <=
      halfTsallisPotentialMass arms
          (sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta 0 sample) / eta n -
        1 / eta n := by
  simpa [sampledScheduledHalfTsallisPotentialPenaltyAtTime,
    sampledScheduledHalfTsallisSameRateNextAt] using
    (sum_halfTsallisCanonicalScheduledPotentialPenalty_pointMass_le
      arms harms eta
        (fun t => sampledScheduledHalfTsallisObservedEstimatedLossAt
          arms harms eta t sample)
        hbest n heta hetaMono)

/-- Generated pathwise best-arm estimated regret is bounded by the scheduled
same-rate stability sum plus the explicit initial-minus-terminal penalty. -/
theorem sampledScheduledHalfTsallisEstimatedRegret_pointMass_le_stability_add_penalty
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real)
    (sample : Env × ((k : Nat) -> Action × Real))
    {best : Action} (hbest : best ∈ arms) (n : Nat)
    (heta : forall t, t <= n -> 0 < eta t)
    (hetaMono : forall t, t < n -> eta (t + 1) <= eta t) :
    sampledScheduledHalfTsallisEstimatedRegret
        arms harms eta (pointMass best) n sample <=
      (Finset.range (n + 1)).sum (fun t =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta sample t) +
        halfTsallisPotentialMass arms
          (sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta 0 sample) / eta n -
        1 / eta n := by
  rw [sampledScheduledHalfTsallisEstimatedRegret_eq_stability_add_penalty]
  have hpenalty :=
    sum_sampledScheduledHalfTsallisPotentialPenalty_pointMass_le
      arms harms eta sample hbest n heta hetaMono
  linarith

end Tsallis
end BanditRLProof
