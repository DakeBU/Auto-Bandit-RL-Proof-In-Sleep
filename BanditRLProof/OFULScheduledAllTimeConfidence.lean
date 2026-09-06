import BanditRLProof.OFULAllTimeConfidence
import BanditRLProof.OFULHistoryEnvironmentRewardLaw

/-!
# Scheduled canonical all-time OFUL confidence

This module defines one history algorithm whose successor selector at history
index `n` uses the confidence budget assigned to horizon `n + 1`.  It then
constructs the corresponding strict-past predictable feature and residual
process and transports the all-time scalar-ridge confidence event to the
actual canonical trajectory.

The final theorem also controls the event that any successor action violates
its scheduled one-step optimism certificate.  A concrete environment-to-
residual-law producer remains a separate law-transport theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u

namespace BanditRLProof
namespace OFUL

/-- History-indexed radius using the budget assigned to successor time `n+1`. -/
noncomputable def finiteHistoryScheduledScalarRidgeRadius
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (lambda S : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n) : Real :=
  finiteHistoryScalarRidgeRadius
    actionFeature R (deltaAt (n + 1)) lambda S n history

/-- Scalar-ridge score with the successor-time confidence schedule. -/
noncomputable def finiteHistoryScheduledScalarRidgeOptimisticScore
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n)
    (action : Fin K) : Real :=
  finiteHistoryOptimisticScore
    (finiteHistoryScalarRidgeEstimate lambda actionFeature)
    (finiteHistoryScalarRidgeDesign lambda actionFeature)
    (finiteHistoryScheduledScalarRidgeRadius
      actionFeature R deltaAt lambda S)
    (finiteHistoryFixedActionFeature actionFeature)
    n history action

theorem finiteHistoryScheduledScalarRidgeOptimisticScore_eq
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n)
    (action : Fin K) :
    finiteHistoryScheduledScalarRidgeOptimisticScore
        lambda actionFeature R deltaAt S n history action =
      finiteHistoryScalarRidgeOptimisticScore
        lambda actionFeature R (deltaAt (n + 1)) S n history action := rfl

/-- Every fixed-action scheduled score is measurable in finite history. -/
theorem measurable_finiteHistoryScheduledScalarRidgeOptimisticScore
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (n : Nat) (action : Fin K) :
    Measurable
      (fun history : History.FinitePairHistory (Fin K) Real n =>
        finiteHistoryScheduledScalarRidgeOptimisticScore
          lambda actionFeature R deltaAt S n history action) := by
  simpa only [finiteHistoryScheduledScalarRidgeOptimisticScore_eq] using
    measurable_finiteHistoryScalarRidgeOptimisticScore
      lambda actionFeature R (deltaAt (n + 1)) S n action

/-- Deterministic strict-fold selector for the scheduled scalar-ridge score. -/
noncomputable def finiteHistoryScheduledScalarRidgeOptimisticAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n) :
    Fin K :=
  finiteHistoryOptimisticAction
    hK
    (finiteHistoryScalarRidgeEstimate lambda actionFeature)
    (finiteHistoryScalarRidgeDesign lambda actionFeature)
    (finiteHistoryScheduledScalarRidgeRadius
      actionFeature R deltaAt lambda S)
    (finiteHistoryFixedActionFeature actionFeature)
    n history

theorem finiteHistoryScheduledScalarRidgeOptimisticAction_eq
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n) :
    finiteHistoryScheduledScalarRidgeOptimisticAction
        hK lambda actionFeature R deltaAt S n history =
      finiteHistoryScalarRidgeOptimisticAction
        hK lambda actionFeature R (deltaAt (n + 1)) S n history := rfl

/-- The scheduled selector maximizes its time-indexed score. -/
theorem finiteHistoryScheduledScalarRidgeOptimisticAction_score_max
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n)
    (action : Fin K) :
    finiteHistoryScheduledScalarRidgeOptimisticScore
        lambda actionFeature R deltaAt S n history action <=
      finiteHistoryScheduledScalarRidgeOptimisticScore
        lambda actionFeature R deltaAt S n history
        (finiteHistoryScheduledScalarRidgeOptimisticAction
          hK lambda actionFeature R deltaAt S n history) := by
  exact finiteHistoryOptimisticAction_score_max
    hK
    (finiteHistoryScalarRidgeEstimate lambda actionFeature)
    (finiteHistoryScalarRidgeDesign lambda actionFeature)
    (finiteHistoryScheduledScalarRidgeRadius
      actionFeature R deltaAt lambda S)
    (finiteHistoryFixedActionFeature actionFeature)
    n history action

/-- One measurable history algorithm using the supplied all-time schedule. -/
noncomputable def finiteHistoryScheduledScalarRidgeOptimisticAlgorithm
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real) :
    Thompson.HistoryAlgorithm (Fin K) Real :=
  finiteHistoryOptimisticAlgorithm
    hK
    (finiteHistoryScalarRidgeEstimate lambda actionFeature)
    (finiteHistoryScalarRidgeDesign lambda actionFeature)
    (finiteHistoryScheduledScalarRidgeRadius
      actionFeature R deltaAt lambda S)
    (finiteHistoryFixedActionFeature actionFeature)
    (measurable_finiteHistoryScheduledScalarRidgeOptimisticScore
      lambda actionFeature R deltaAt S)

/-- Scheduled algorithm specialized to the exact telescoping confidence budget. -/
noncomputable def finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) :
    Thompson.HistoryAlgorithm (Fin K) Real :=
  finiteHistoryScheduledScalarRidgeOptimisticAlgorithm
    hK lambda actionFeature R (allTimeTelescopingDelta delta) S

/-- The telescoping scheduled policy starts from the fixed canonical arm. -/
theorem finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm_initialAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) :
    (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
      hK lambda actionFeature R delta S).initialAction =
      Measure.dirac ⟨0, hK⟩ := rfl

/--
The scheduled history-step reward marginal is the environment feedback law at
the scheduled selected action.
-/
theorem finiteHistoryScheduledScalarRidge_historyStepKernel_map_snd
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n) :
    (Thompson.historyStepKernel
        (finiteHistoryScheduledScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R deltaAt S)
        environment n).map Prod.snd history =
      environment.feedback n
        (history,
          finiteHistoryScheduledScalarRidgeOptimisticAction
            hK lambda actionFeature R deltaAt S n history) := by
  ext s hs
  rw [ProbabilityTheory.Kernel.map_apply _ measurable_snd,
    Measure.map_apply measurable_snd hs]
  unfold Thompson.historyStepKernel
  rw [ProbabilityTheory.Kernel.compProd_apply (measurable_snd hs)]
  simp only [finiteHistoryScheduledScalarRidgeOptimisticAlgorithm,
    finiteHistoryScheduledScalarRidgeOptimisticAction,
    finiteHistoryOptimisticAlgorithm_policy_apply]
  rw [lintegral_dirac]
  let selected :=
    finiteHistoryOptimisticAction hK
      (finiteHistoryScalarRidgeEstimate lambda actionFeature)
      (finiteHistoryScalarRidgeDesign lambda actionFeature)
      (finiteHistoryScheduledScalarRidgeRadius
        actionFeature R deltaAt lambda S)
      (finiteHistoryFixedActionFeature actionFeature) n history
  change environment.feedback n (history, selected)
      (Prod.mk selected ⁻¹' (Prod.snd ⁻¹' s)) =
    environment.feedback n (history, selected) s
  have hpreimage :
      Prod.mk selected ⁻¹' (Prod.snd ⁻¹' s) = s := by
    ext reward
    rfl
  rw [hpreimage]

/-- Feature selected from the scheduled finite-history ridge state. -/
noncomputable def finiteHistoryScheduledScalarRidgeSelectedFeature
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n) :
    Feature -> Real :=
  actionFeature
    (finiteHistoryScheduledScalarRidgeOptimisticAction
      hK lambda actionFeature R deltaAt S n history)

/-- The actual canonical successor feature agrees with the scheduled selector. -/
theorem
    canonicalHistoryTrajectory_observedFeature_succ_ae_eq_scheduledSelectedFeature
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScheduledScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R deltaAt S)
          environment,
      actionFeature
          (Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1)) =
        finiteHistoryScheduledScalarRidgeSelectedFeature
          hK lambda actionFeature R deltaAt S n
          (History.finitePairHistoryOfTrace
            (Thompson.canonicalHistoryTrajectoryAction trajectory)
            (Thompson.canonicalHistoryTrajectoryReward trajectory) n) := by
  simpa only [finiteHistoryScheduledScalarRidgeOptimisticAlgorithm,
    finiteHistoryScheduledScalarRidgeSelectedFeature,
    finiteHistoryScheduledScalarRidgeOptimisticAction,
    finiteHistoryFixedActionFeature,
    finiteHistoryOptimisticSelectedFeature] using
    canonicalHistoryTrajectory_candidateFeature_succ_ae_eq_selectedFeature
      hK
      (finiteHistoryScalarRidgeEstimate lambda actionFeature)
      (finiteHistoryScalarRidgeDesign lambda actionFeature)
      (finiteHistoryScheduledScalarRidgeRadius
        actionFeature R deltaAt lambda S)
      (finiteHistoryFixedActionFeature actionFeature)
      (measurable_finiteHistoryScheduledScalarRidgeOptimisticScore
        lambda actionFeature R deltaAt S)
      environment n

/-- The scheduled selector is measurable in its finite history. -/
theorem measurable_finiteHistoryScheduledScalarRidgeOptimisticAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (n : Nat) :
    Measurable
      (finiteHistoryScheduledScalarRidgeOptimisticAction
        hK lambda actionFeature R deltaAt S n) := by
  simpa only [finiteHistoryScheduledScalarRidgeOptimisticAction,
    finiteHistoryScheduledScalarRidgeOptimisticScore] using
    measurable_finiteHistoryOptimisticAction
      hK
      (finiteHistoryScalarRidgeEstimate lambda actionFeature)
      (finiteHistoryScalarRidgeDesign lambda actionFeature)
      (finiteHistoryScheduledScalarRidgeRadius
        actionFeature R deltaAt lambda S)
      (finiteHistoryFixedActionFeature actionFeature)
      n
      (measurable_finiteHistoryScheduledScalarRidgeOptimisticScore
        lambda actionFeature R deltaAt S n)

/-- Strict-past scheduled feature process on the canonical trajectory space. -/
noncomputable def scheduledCanonicalHistoryTrajectoryPredictableFeature
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real) :
    Nat -> (Nat -> Fin K × Real) -> Feature -> Real
  | 0, _trajectory =>
      actionFeature ⟨0, hK⟩
  | n + 1, trajectory =>
      finiteHistoryScheduledScalarRidgeSelectedFeature
        hK lambda actionFeature R deltaAt S n
        (Preorder.frestrictLe n trajectory)

/-- Every scheduled predictable-feature coordinate is strict-past measurable. -/
theorem
    scheduledCanonicalHistoryTrajectoryPredictableFeature_stronglyMeasurable
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (t : Nat) (j : Feature) :
    StronglyMeasurable[
      canonicalHistoryTrajectoryBeforeFiltration (K := K) t]
      (fun trajectory =>
        scheduledCanonicalHistoryTrajectoryPredictableFeature
          hK lambda actionFeature R deltaAt S t trajectory j) := by
  cases t with
  | zero =>
      exact stronglyMeasurable_const
  | succ n =>
      let F := canonicalHistoryTrajectoryBeforeFiltration (K := K)
      have hprefix :
          @Measurable (Nat -> Fin K × Real)
            ((i : Finset.Iic n) -> Fin K × Real)
            (F (n + 1)) inferInstance
            (Preorder.frestrictLe n) := by
        rw [canonicalHistoryTrajectoryBeforeFiltration_succ,
          Filtration.piLE_eq_comap_frestrictLe]
        exact Measurable.of_comap_le le_rfl
      have hselector :
          Measurable
            (finiteHistoryScheduledScalarRidgeOptimisticAction
              hK lambda actionFeature R deltaAt S n) :=
        measurable_finiteHistoryScheduledScalarRidgeOptimisticAction
          hK lambda actionFeature R deltaAt S n
      have hfeature :
          Measurable
            (fun history : History.FinitePairHistory (Fin K) Real n =>
              actionFeature
                (finiteHistoryScheduledScalarRidgeOptimisticAction
                  hK lambda actionFeature R deltaAt S n history) j) :=
        (measurable_of_countable
          (fun action : Fin K => actionFeature action j)).comp hselector
      exact (hfeature.comp hprefix).stronglyMeasurable

/-- The scheduled algorithm starts from the same deterministic arm. -/
theorem
    scheduledCanonicalHistoryTrajectory_action_zero_ae_eq_initialArm
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScheduledScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R deltaAt S)
          environment,
      Thompson.canonicalHistoryTrajectoryAction trajectory 0 = ⟨0, hK⟩ := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  let algorithm :=
    finiteHistoryScheduledScalarRidgeOptimisticAlgorithm
      hK lambda actionFeature R deltaAt S
  let mu := Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
  have hmap :
      Measure.map
          (fun trajectory =>
            Thompson.canonicalHistoryTrajectoryAction trajectory 0)
          mu =
        Measure.dirac (⟨0, hK⟩ : Fin K) := by
    have h :=
      Thompson.initialAction_map_eq_of_historyAlgorithmEnvironmentSequence
        mu
        Thompson.canonicalHistoryTrajectoryAction
        Thompson.canonicalHistoryTrajectoryReward
        algorithm environment
        (Thompson.canonicalHistoryAlgorithmEnvironmentSequence
          algorithm environment)
    simpa [algorithm, finiteHistoryScheduledScalarRidgeOptimisticAlgorithm,
      finiteHistoryOptimisticAlgorithm] using h
  have hmap_ae :
      ∀ᵐ action ∂
          Measure.map
            (fun trajectory =>
              Thompson.canonicalHistoryTrajectoryAction trajectory 0)
            mu,
        action = (⟨0, hK⟩ : Fin K) := by
    rw [hmap]
    simp
  exact
    (ae_map_iff
      (Thompson.measurable_canonicalHistoryTrajectoryAction_apply
        0).aemeasurable
      (by measurability)).mp hmap_ae

/-- Actual and scheduled predictable features agree at each time. -/
theorem
    canonicalHistoryTrajectoryFeature_ae_eq_scheduledPredictableFeature
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (t : Nat) :
    canonicalHistoryTrajectoryFeature actionFeature t =ᵐ[
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScheduledScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R deltaAt S)
        environment]
      scheduledCanonicalHistoryTrajectoryPredictableFeature
        hK lambda actionFeature R deltaAt S t := by
  cases t with
  | zero =>
      filter_upwards [
        scheduledCanonicalHistoryTrajectory_action_zero_ae_eq_initialArm
          hK lambda actionFeature R deltaAt S environment] with
        trajectory htrajectory
      simp [canonicalHistoryTrajectoryFeature,
        scheduledCanonicalHistoryTrajectoryPredictableFeature, htrajectory]
  | succ n =>
      simpa [canonicalHistoryTrajectoryFeature,
        scheduledCanonicalHistoryTrajectoryPredictableFeature,
        History.finitePairHistoryOfTrace,
        Thompson.canonicalHistoryTrajectoryAction,
        Thompson.canonicalHistoryTrajectoryReward,
        Preorder.frestrictLe] using
        canonicalHistoryTrajectory_observedFeature_succ_ae_eq_scheduledSelectedFeature
          hK lambda actionFeature R deltaAt S environment n

/-- Actual and scheduled predictable features agree simultaneously. -/
theorem
    canonicalHistoryTrajectoryFeature_ae_eq_scheduledPredictableFeature_all
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScheduledScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R deltaAt S)
          environment,
      ∀ t,
        canonicalHistoryTrajectoryFeature actionFeature t trajectory =
          scheduledCanonicalHistoryTrajectoryPredictableFeature
            hK lambda actionFeature R deltaAt S t trajectory := by
  rw [ae_all_iff]
  exact
    canonicalHistoryTrajectoryFeature_ae_eq_scheduledPredictableFeature
      hK lambda actionFeature R deltaAt S environment

/-- Reward residual around the scheduled strict-past selected feature. -/
noncomputable def scheduledCanonicalHistoryTrajectoryPredictableResidual
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (i : Nat) (trajectory : Nat -> Fin K × Real) : Real :=
  canonicalHistoryTrajectoryResponse i trajectory -
    dotProduct thetaStar
      (scheduledCanonicalHistoryTrajectoryPredictableFeature
        hK lambda actionFeature R deltaAt S i trajectory)

/-- The zero-initialized scheduled residual process is strongly adapted. -/
theorem
    scheduledCanonicalHistoryTrajectoryPredictableResidual_stronglyAdapted
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real) :
    StronglyAdapted
      (canonicalHistoryTrajectoryBeforeFiltration (K := K))
      (fun t trajectory =>
        match t with
        | 0 => 0
        | i + 1 =>
            scheduledCanonicalHistoryTrajectoryPredictableResidual
              hK lambda thetaStar actionFeature R deltaAt S i trajectory) := by
  let F := canonicalHistoryTrajectoryBeforeFiltration (K := K)
  intro t
  cases t with
  | zero =>
      exact stronglyMeasurable_const
  | succ i =>
      have hresponse :
          StronglyMeasurable[F (i + 1)]
            (canonicalHistoryTrajectoryResponse i) :=
        (measurable_canonicalHistoryTrajectoryResponse_before_succ
          (K := K) i).stronglyMeasurable
      have hfeature : forall j,
          StronglyMeasurable[F (i + 1)]
            (fun trajectory =>
              scheduledCanonicalHistoryTrajectoryPredictableFeature
                hK lambda actionFeature R deltaAt S i trajectory j) := by
        intro j
        exact
          (scheduledCanonicalHistoryTrajectoryPredictableFeature_stronglyMeasurable
            hK lambda actionFeature R deltaAt S i j).mono
            (F.mono (Nat.le_succ i))
      have hdot :
          StronglyMeasurable[F (i + 1)]
            (fun trajectory =>
              dotProduct thetaStar
                (scheduledCanonicalHistoryTrajectoryPredictableFeature
                  hK lambda actionFeature R deltaAt S i trajectory)) := by
        have hsum :=
          Finset.stronglyMeasurable_sum
            (Finset.univ : Finset Feature) fun j _ =>
              (stronglyMeasurable_const :
                  StronglyMeasurable[F (i + 1)]
                    (fun _trajectory : Nat -> Fin K × Real =>
                      thetaStar j)).mul
                (hfeature j)
        convert hsum using 1
        funext trajectory
        simp [dotProduct, Finset.sum_apply]
      simpa [F,
        scheduledCanonicalHistoryTrajectoryPredictableResidual] using
        hresponse.sub hdot

/-- Scheduled selected features obey the same finite-action projection cap. -/
theorem
    scheduledPredictableFeature_projection_le_finiteActionProjectionBound
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (deltaAt : Nat -> Real) (S : Real)
    (theta : EuclideanSpace Real Feature)
    (i : Nat) (trajectory : Nat -> Fin K × Real) :
    |dotProduct (WithLp.ofLp theta)
        (scheduledCanonicalHistoryTrajectoryPredictableFeature
          hK lambda actionFeature R deltaAt S i trajectory)| <=
      finiteActionProjectionBound hK actionFeature theta := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  cases i with
  | zero =>
      simpa [scheduledCanonicalHistoryTrajectoryPredictableFeature,
        finiteActionProjectionBound] using
        (Finset.le_sup'
          (s := (Finset.univ : Finset (Fin K)))
          (f := fun action =>
            |dotProduct (WithLp.ofLp theta) (actionFeature action)|)
          (Finset.mem_univ (⟨0, hK⟩ : Fin K)))
  | succ n =>
      simpa [scheduledCanonicalHistoryTrajectoryPredictableFeature,
        finiteHistoryScheduledScalarRidgeSelectedFeature,
        finiteActionProjectionBound] using
        (Finset.le_sup'
          (s := (Finset.univ : Finset (Fin K)))
          (f := fun action =>
            |dotProduct (WithLp.ofLp theta) (actionFeature action)|)
          (Finset.mem_univ
            (finiteHistoryScheduledScalarRidgeOptimisticAction
              hK lambda actionFeature R deltaAt S n
              (Preorder.frestrictLe n trajectory))))

/--
All stochastic input needed by scheduled canonical all-time confidence.

The field is intentionally all-time and is stated on the one trajectory
measure generated by the telescoping-schedule algorithm.
-/
structure CanonicalScheduledPredictableScalarRidgeResidualLaw
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real) : Prop where
  theta_norm_le : euclideanLength thetaStar <= S
  residual_hasCondSubgaussianMGF : forall i,
    HasCondSubgaussianMGF
      (canonicalHistoryTrajectoryBeforeFiltration (K := K) i)
      ((canonicalHistoryTrajectoryBeforeFiltration (K := K)).le i)
      (scheduledCanonicalHistoryTrajectoryPredictableResidual
        hK lambda thetaStar actionFeature R
          (allTimeTelescopingDelta delta) S i)
      (constantSquaredVarianceProxy R i)
      (Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment)

/--
The kernel-level linear sub-Gaussian environment contract constructs the
all-time predictable residual law for the single telescoping scheduled policy.
-/
noncomputable def
    canonicalScheduledPredictableScalarRidgeResidualLaw_of_linearSubgaussianEnvironment
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    CanonicalScheduledPredictableScalarRidgeResidualLaw
      hK lambda thetaStar actionFeature R delta S environment where
  theta_norm_le := source.theta_norm_le
  residual_hasCondSubgaussianMGF i := by
    let algorithm :=
      finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
        hK lambda actionFeature R delta S
    let mu := Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
    cases i with
    | zero =>
        let condition : (Nat -> Fin K × Real) -> Unit := fun _trajectory => ()
        let mcond :=
          (inferInstance : MeasurableSpace Unit).comap condition
        let reward0 : (Nat -> Fin K × Real) -> Real :=
          fun trajectory => (trajectory 0).2
        let center0 : (Nat -> Fin K × Real) -> Real :=
          fun _trajectory =>
            dotProduct thetaStar (actionFeature ⟨0, hK⟩)
        have hmcond :
            mcond <=
              (MeasurableSpace.pi :
                MeasurableSpace (Nat -> Fin K × Real)) := by
          exact measurable_const.comap_le
        have hrewardLaw :
            Filter.Eventually
              (fun trajectory : Nat -> Fin K × Real =>
                @Measure.map (Nat -> Fin K × Real) Real
                    MeasurableSpace.pi inferInstance reward0
                    (@ProbabilityTheory.condExpKernel
                      (Nat -> Fin K × Real) MeasurableSpace.pi _ mu _
                      mcond trajectory) =
                  environment.initialFeedback ⟨0, hK⟩)
              (ae (@Measure.trim (Nat -> Fin K × Real)
                mcond MeasurableSpace.pi mu hmcond)) := by
          simpa [mu, algorithm, mcond, condition, reward0] using
            canonicalHistoryTrajectory_initialReward_condExpKernel_map_eq_historyAlgorithmInitialFeedback_unitComap
              algorithm ⟨0, hK⟩
                (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm_initialAction
                  hK lambda actionFeature R delta S)
              environment
        have htargetLaw :
            Filter.Eventually
              (fun _trajectory : Nat -> Fin K × Real =>
                ProbabilityTheory.HasSubgaussianMGF
                  (fun reward => reward - center0 _trajectory)
                  (constantSquaredVarianceProxy R 0)
                  (environment.initialFeedback ⟨0, hK⟩))
              (ae (@Measure.trim (Nat -> Fin K × Real)
                mcond MeasurableSpace.pi mu hmcond)) :=
          Filter.Eventually.of_forall (fun _trajectory =>
            source.initial_reward_hasSubgaussianMGF)
        have hconditional :=
          ConditionalExpectationReward.hasCondSubgaussianMGF_centered_of_condExpKernel_map_eq
            (mOmega := MeasurableSpace.pi)
            mu mcond hmcond reward0 center0
            (constantSquaredVarianceProxy R 0)
            (measurable_snd.comp (measurable_pi_apply 0))
            measurable_const
            (fun _trajectory => environment.initialFeedback ⟨0, hK⟩)
            hrewardLaw htargetLaw
        simpa [mu, algorithm, mcond, condition, reward0, center0,
          scheduledCanonicalHistoryTrajectoryPredictableResidual,
          canonicalHistoryTrajectoryResponse,
          scheduledCanonicalHistoryTrajectoryPredictableFeature,
          MeasurableSpace.comap_const] using hconditional
    | succ n =>
        let history : (Nat -> Fin K × Real) ->
            History.FinitePairHistory (Fin K) Real n :=
          Preorder.frestrictLe n
        let mcond :=
          (inferInstance :
            MeasurableSpace
              (History.FinitePairHistory (Fin K) Real n)).comap history
        let response : (Nat -> Fin K × Real) -> Real :=
          fun trajectory => (trajectory (n + 1)).2
        let center : (Nat -> Fin K × Real) -> Real :=
          fun trajectory =>
            dotProduct thetaStar
              (scheduledCanonicalHistoryTrajectoryPredictableFeature
                hK lambda actionFeature R
                  (allTimeTelescopingDelta delta) S
                (n + 1) trajectory)
        let stepRewardKernel :=
          (Thompson.historyStepKernel algorithm environment n).map Prod.snd
        let target : (Nat -> Fin K × Real) -> Measure Real :=
          fun trajectory => stepRewardKernel (history trajectory)
        have hmcond :
            mcond <=
              (MeasurableSpace.pi :
                MeasurableSpace (Nat -> Fin K × Real)) := by
          simpa [mcond, history] using
            (Preorder.measurable_frestrictLe
              (X := fun _ : Nat => Fin K × Real) n).comap_le
        have hcenterF :
            @Measurable (Nat -> Fin K × Real) Real
              (canonicalHistoryTrajectoryBeforeFiltration (K := K) (n + 1))
              inferInstance center := by
          have hcoordinates : forall j,
              StronglyMeasurable[
                canonicalHistoryTrajectoryBeforeFiltration (K := K) (n + 1)]
                (fun trajectory =>
                  scheduledCanonicalHistoryTrajectoryPredictableFeature
                    hK lambda actionFeature R
                      (allTimeTelescopingDelta delta) S
                    (n + 1) trajectory j) := by
            intro j
            exact
              scheduledCanonicalHistoryTrajectoryPredictableFeature_stronglyMeasurable
                hK lambda actionFeature R
                  (allTimeTelescopingDelta delta) S (n + 1) j
          have hsum :=
            Finset.stronglyMeasurable_sum
              (Finset.univ : Finset Feature) fun j _ =>
                (stronglyMeasurable_const :
                  StronglyMeasurable[
                    canonicalHistoryTrajectoryBeforeFiltration
                      (K := K) (n + 1)]
                    (fun _trajectory : Nat -> Fin K × Real =>
                      thetaStar j)).mul
                  (hcoordinates j)
          convert hsum.measurable using 1
          funext trajectory
          simp [center, dotProduct, Finset.sum_apply]
        have hfiltration :
            (canonicalHistoryTrajectoryBeforeFiltration (K := K) (n + 1) :
                MeasurableSpace (Nat -> Fin K × Real)) = mcond := by
          simp [mcond, history,
            canonicalHistoryTrajectoryBeforeFiltration_succ,
            Filtration.piLE_eq_comap_frestrictLe]
        have hcenter : @Measurable (Nat -> Fin K × Real) Real
            mcond inferInstance center := by
          rw [← hfiltration]
          exact hcenterF
        have hrewardLaw :
            Filter.Eventually
              (fun trajectory : Nat -> Fin K × Real =>
                @Measure.map (Nat -> Fin K × Real) Real
                    MeasurableSpace.pi inferInstance response
                    (@ProbabilityTheory.condExpKernel
                      (Nat -> Fin K × Real) MeasurableSpace.pi _ mu _
                      mcond trajectory) =
                  target trajectory)
              (ae (@Measure.trim (Nat -> Fin K × Real)
                mcond MeasurableSpace.pi mu hmcond)) := by
          simpa [mu, algorithm, mcond, history, response, target,
            stepRewardKernel] using
            canonicalHistoryTrajectory_reward_succ_condExpKernel_map_eq_historyStepReward_comap
              hK algorithm environment n
        have htargetLaw :
            Filter.Eventually
              (fun trajectory : Nat -> Fin K × Real =>
                ProbabilityTheory.HasSubgaussianMGF
                  (fun reward => reward - center trajectory)
                  (constantSquaredVarianceProxy R (n + 1))
                  (target trajectory))
              (ae (@Measure.trim (Nat -> Fin K × Real)
                mcond MeasurableSpace.pi mu hmcond)) := by
          refine Filter.Eventually.of_forall (fun trajectory => ?_)
          rw [show target trajectory =
              environment.feedback n
                (history trajectory,
                  finiteHistoryScheduledScalarRidgeOptimisticAction
                    hK lambda actionFeature R
                      (allTimeTelescopingDelta delta) S n
                      (history trajectory)) by
            exact finiteHistoryScheduledScalarRidge_historyStepKernel_map_snd
              hK lambda actionFeature R (allTimeTelescopingDelta delta) S
                environment n (history trajectory)]
          simpa [center, history,
            scheduledCanonicalHistoryTrajectoryPredictableFeature,
            finiteHistoryScheduledScalarRidgeSelectedFeature] using
            source.feedback_reward_hasSubgaussianMGF n (history trajectory)
              (finiteHistoryScheduledScalarRidgeOptimisticAction
                hK lambda actionFeature R
                  (allTimeTelescopingDelta delta) S n
                  (history trajectory))
        have hconditional :=
          ConditionalExpectationReward.hasCondSubgaussianMGF_centered_of_condExpKernel_map_eq
            (mOmega := MeasurableSpace.pi)
            mu mcond hmcond response center
            (constantSquaredVarianceProxy R (n + 1))
            (measurable_snd.comp (measurable_pi_apply (n + 1)))
            hcenter target hrewardLaw htargetLaw
        have hconditionalF :=
          ConditionalExpectationReward.hasCondSubgaussianMGF_congr_measurableSpace
            (mOmega := MeasurableSpace.pi) mu mcond
            (canonicalHistoryTrajectoryBeforeFiltration (K := K) (n + 1))
            hmcond
            ((canonicalHistoryTrajectoryBeforeFiltration (K := K)).le (n + 1))
            hfiltration.symm
            (fun trajectory => response trajectory - center trajectory)
            (constantSquaredVarianceProxy R (n + 1)) hconditional
        simpa [mu, algorithm, response, center,
          scheduledCanonicalHistoryTrajectoryPredictableResidual] using hconditionalF

/-- Pointwise feature equality preserves the countable telescoping event. -/
theorem
    mem_allTimeTelescopingScalarRidgeConfidenceFailureSet_iff_of_feature_eq
    {Omega : Type*} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (S : Real)
    (feature feature' : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (R delta : Real)
    (omega : Omega)
    (hfeature : forall i, feature i omega = feature' i omega) :
    omega ∈
        allTimeTelescopingScalarRidgeConfidenceFailureSet
          lambda thetaStar S feature response R delta ↔
      omega ∈
        allTimeTelescopingScalarRidgeConfidenceFailureSet
          lambda thetaStar S feature' response R delta := by
  simp only [allTimeTelescopingScalarRidgeConfidenceFailureSet,
    mem_allTimeScheduledScalarRidgeConfidenceFailureSet_iff]
  constructor
  · rintro ⟨n, hfailure⟩
    exact ⟨n,
      (mem_scalarRidgeConfidenceFailureAt_iff_of_feature_eq
        lambda thetaStar S feature feature' response R
        (allTimeTelescopingDelta delta n) n omega hfeature).mp hfailure⟩
  · rintro ⟨n, hfailure⟩
    exact ⟨n,
      (mem_scalarRidgeConfidenceFailureAt_iff_of_feature_eq
        lambda thetaStar S feature feature' response R
        (allTimeTelescopingDelta delta n) n omega hfeature).mpr hfailure⟩

/--
The scheduled canonical trajectory satisfies all deterministic-horizon
scalar-ridge confidence ellipsoids outside one event of probability `delta`.
-/
theorem
    measure_telescopingCanonicalHistoryTrajectory_allTimeConfidenceFailureSet_le
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (source : CanonicalScheduledPredictableScalarRidgeResidualLaw
      hK lambda thetaStar actionFeature R delta S environment) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
        (allTimeTelescopingScalarRidgeConfidenceFailureSet
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse R delta) <=
      ENNReal.ofReal delta := by
  let deltaAt := allTimeTelescopingDelta delta
  let algorithm :=
    finiteHistoryScheduledScalarRidgeOptimisticAlgorithm
      hK lambda actionFeature R deltaAt S
  let mu := Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
  let F := canonicalHistoryTrajectoryBeforeFiltration (K := K)
  let predictableFeature :=
    scheduledCanonicalHistoryTrajectoryPredictableFeature
      hK lambda actionFeature R deltaAt S
  let residual :=
    scheduledCanonicalHistoryTrajectoryPredictableResidual
      hK lambda thetaStar actionFeature R deltaAt S
  have hpredictable :
      mu
          (allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S predictableFeature
            canonicalHistoryTrajectoryResponse R delta) <=
        ENNReal.ofReal delta := by
    apply
      measure_allTimeTelescopingScalarRidgeConfidenceFailureSet_le
        mu lambda hlambda thetaStar S source.theta_norm_le F
        predictableFeature canonicalHistoryTrajectoryResponse residual
        R hR
        (fun theta _i =>
          finiteActionProjectionBound hK actionFeature theta)
    · intro i j
      exact
        scheduledCanonicalHistoryTrajectoryPredictableFeature_stronglyMeasurable
          hK lambda actionFeature R deltaAt S i j
    · exact
        scheduledCanonicalHistoryTrajectoryPredictableResidual_stronglyAdapted
          hK lambda thetaStar actionFeature R deltaAt S
    · intro theta i
      exact finiteActionProjectionBound_nonneg hK actionFeature theta
    · intro theta i trajectory
      exact
        scheduledPredictableFeature_projection_le_finiteActionProjectionBound
          hK lambda actionFeature R deltaAt S theta i trajectory
    · intro i
      simpa [mu, algorithm, deltaAt, residual,
        finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm] using
        source.residual_hasCondSubgaussianMGF i
    · intro trajectory i
      simp [residual, predictableFeature,
        scheduledCanonicalHistoryTrajectoryPredictableResidual]
    · exact hdelta
    · exact hdelta_one
  have hevents :
      ∀ᵐ trajectory ∂mu,
        trajectory ∈
            allTimeTelescopingScalarRidgeConfidenceFailureSet
              lambda thetaStar S
              (canonicalHistoryTrajectoryFeature actionFeature)
              canonicalHistoryTrajectoryResponse R delta ↔
          trajectory ∈
            allTimeTelescopingScalarRidgeConfidenceFailureSet
              lambda thetaStar S predictableFeature
              canonicalHistoryTrajectoryResponse R delta := by
    filter_upwards [
      canonicalHistoryTrajectoryFeature_ae_eq_scheduledPredictableFeature_all
        hK lambda actionFeature R deltaAt S environment] with
      trajectory htrajectory
    exact
      mem_allTimeTelescopingScalarRidgeConfidenceFailureSet_iff_of_feature_eq
        lambda thetaStar S
        (canonicalHistoryTrajectoryFeature actionFeature)
        predictableFeature canonicalHistoryTrajectoryResponse
        R delta trajectory htrajectory
  change
    mu
        (allTimeTelescopingScalarRidgeConfidenceFailureSet
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse R delta) <=
      ENNReal.ofReal delta
  calc
    mu
        (allTimeTelescopingScalarRidgeConfidenceFailureSet
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse R delta) =
        mu
          (allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S predictableFeature
            canonicalHistoryTrajectoryResponse R delta) :=
      measure_congr (hevents.mono fun _ h => propext h)
    _ <= ENNReal.ofReal delta := hpredictable

/-- The actual successor action agrees with the scheduled strict-fold action. -/
theorem
    telescopingCanonicalHistoryTrajectory_action_succ_ae_eq_scheduledAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment,
      Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1) =
        finiteHistoryScheduledScalarRidgeOptimisticAction
          hK lambda actionFeature R
          (allTimeTelescopingDelta delta) S n
          (History.finitePairHistoryOfTrace
            (Thompson.canonicalHistoryTrajectoryAction trajectory)
            (Thompson.canonicalHistoryTrajectoryReward trajectory) n) := by
  simpa only [finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm,
    finiteHistoryScheduledScalarRidgeOptimisticAlgorithm,
    finiteHistoryScheduledScalarRidgeOptimisticAction] using
    canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryOptimisticAction
      hK
      (finiteHistoryScalarRidgeEstimate lambda actionFeature)
      (finiteHistoryScalarRidgeDesign lambda actionFeature)
      (finiteHistoryScheduledScalarRidgeRadius actionFeature R
        (allTimeTelescopingDelta delta) lambda S)
      (finiteHistoryFixedActionFeature actionFeature)
      (measurable_finiteHistoryScheduledScalarRidgeOptimisticScore
        lambda actionFeature R (allTimeTelescopingDelta delta) S)
      environment n

/--
Outside the scheduled fixed-time confidence failure, the actual successor
action satisfies the matching time-indexed optimism-gap certificate.
-/
theorem
    telescopingCanonicalHistoryTrajectory_action_succ_gap_le_of_not_mem_confidenceFailure
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (n : Nat) (comparator : Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment,
      trajectory ∉
          scalarRidgeConfidenceFailureAt
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse R
            (allTimeTelescopingDelta delta (n + 1)) (n + 1) ->
        linearValue thetaStar (actionFeature comparator) -
            linearValue thetaStar
              (actionFeature
                (Thompson.canonicalHistoryTrajectoryAction
                  trajectory (n + 1))) <=
          2 *
            finiteHorizonScalarConfidenceRadius
              (canonicalHistoryTrajectoryFeature actionFeature)
              R (allTimeTelescopingDelta delta (n + 1))
              lambda S (n + 1) trajectory *
            confidenceWidth
              (finiteHorizonScalarGram lambda
                (canonicalHistoryTrajectoryFeature actionFeature)
                (n + 1) trajectory)
              (actionFeature
                (Thompson.canonicalHistoryTrajectoryAction
                  trajectory (n + 1))) := by
  filter_upwards [
    telescopingCanonicalHistoryTrajectory_action_succ_ae_eq_scheduledAction
      hK lambda actionFeature R delta S environment n] with
    trajectory haction
  intro hgood
  let history :=
    History.finitePairHistoryOfTrace
      (Thompson.canonicalHistoryTrajectoryAction trajectory)
      (Thompson.canonicalHistoryTrajectoryReward trajectory) n
  let deltaN := allTimeTelescopingDelta delta (n + 1)
  have hgeneric :
      matrixNorm
          (finiteHorizonScalarGram lambda
            (canonicalHistoryTrajectoryFeature actionFeature)
            (n + 1) trajectory)
          (finiteHorizonRidgeEstimate
              (Matrix.scalar Feature lambda)
              (canonicalHistoryTrajectoryFeature actionFeature)
              canonicalHistoryTrajectoryResponse
              (n + 1) trajectory -
            thetaStar) <=
        finiteHorizonScalarConfidenceRadius
          (canonicalHistoryTrajectoryFeature actionFeature)
          R deltaN lambda S (n + 1) trajectory := by
    simpa only [deltaN, scalarRidgeConfidenceFailureAt,
      finiteHorizonScalarGram, Set.mem_setOf_eq, not_lt] using hgood
  have hhistory :
      matrixNorm
          (finiteHistoryScalarRidgeDesign
            lambda actionFeature n history)
          (finiteHistoryScalarRidgeEstimate
              lambda actionFeature n history -
            thetaStar) <=
        finiteHistoryScalarRidgeRadius
          actionFeature R deltaN lambda S n history := by
    simpa only [history,
      finiteHistoryScalarRidgeDesign_finitePairHistoryOfTrace_eq,
      finiteHistoryScalarRidgeEstimate_finitePairHistoryOfTrace_eq,
      finiteHistoryScalarRidgeRadius_finitePairHistoryOfTrace_eq] using
      hgeneric
  have hgap :=
    finiteHistoryScalarRidgeOptimisticAction_gap_le
      hK lambda hlambda thetaStar actionFeature R deltaN S n history
      hhistory comparator
  have haction' :
      Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1) =
        finiteHistoryScalarRidgeOptimisticAction
          hK lambda actionFeature R deltaN S n history := by
    simpa only [history, deltaN,
      finiteHistoryScheduledScalarRidgeOptimisticAction_eq] using haction
  rw [← haction'] at hgap
  simpa only [history, deltaN,
    finiteHistoryScalarRidgeDesign_finitePairHistoryOfTrace_eq,
    finiteHistoryScalarRidgeRadius_finitePairHistoryOfTrace_eq] using hgap

/-- Event that some successor action violates its scheduled optimism bound. -/
def telescopingCanonicalHistoryTrajectoryAllTimeSuccGapViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (comparator : Nat -> Fin K) :
    Set (Nat -> Fin K × Real) :=
  {trajectory | ∃ n,
    2 *
        finiteHorizonScalarConfidenceRadius
          (canonicalHistoryTrajectoryFeature actionFeature)
          R (allTimeTelescopingDelta delta (n + 1))
          lambda S (n + 1) trajectory *
        confidenceWidth
          (finiteHorizonScalarGram lambda
            (canonicalHistoryTrajectoryFeature actionFeature)
            (n + 1) trajectory)
          (actionFeature
            (Thompson.canonicalHistoryTrajectoryAction
              trajectory (n + 1))) <
      linearValue thetaStar (actionFeature (comparator (n + 1))) -
        linearValue thetaStar
          (actionFeature
            (Thompson.canonicalHistoryTrajectoryAction
              trajectory (n + 1)))}

/-- Any scheduled successor-gap violation forces a confidence failure a.e. -/
theorem
    telescopingCanonicalHistoryTrajectoryAllTimeSuccGapViolationSet_subset_confidenceFailure_ae
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (comparator : Nat -> Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment,
      trajectory ∈
          telescopingCanonicalHistoryTrajectoryAllTimeSuccGapViolationSet
            lambda thetaStar actionFeature R delta S comparator ->
        trajectory ∈
          allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse R delta := by
  have hall :
      ∀ᵐ trajectory ∂
          Thompson.canonicalHistoryTrajectoryMeasure
            (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
              hK lambda actionFeature R delta S)
            environment,
        ∀ n,
          trajectory ∉
              scalarRidgeConfidenceFailureAt
                lambda thetaStar S
                (canonicalHistoryTrajectoryFeature actionFeature)
                canonicalHistoryTrajectoryResponse R
                (allTimeTelescopingDelta delta (n + 1)) (n + 1) ->
            linearValue thetaStar
                (actionFeature (comparator (n + 1))) -
                linearValue thetaStar
                  (actionFeature
                    (Thompson.canonicalHistoryTrajectoryAction
                      trajectory (n + 1))) <=
              2 *
                finiteHorizonScalarConfidenceRadius
                  (canonicalHistoryTrajectoryFeature actionFeature)
                  R (allTimeTelescopingDelta delta (n + 1))
                  lambda S (n + 1) trajectory *
                confidenceWidth
                  (finiteHorizonScalarGram lambda
                    (canonicalHistoryTrajectoryFeature actionFeature)
                    (n + 1) trajectory)
                  (actionFeature
                    (Thompson.canonicalHistoryTrajectoryAction
                      trajectory (n + 1))) := by
    rw [ae_all_iff]
    intro n
    exact
      telescopingCanonicalHistoryTrajectory_action_succ_gap_le_of_not_mem_confidenceFailure
        hK lambda hlambda thetaStar actionFeature R delta S
        environment n (comparator (n + 1))
  filter_upwards [hall] with trajectory htrajectory
  rintro ⟨n, hviolation⟩
  have hfailure :
      trajectory ∈
        scalarRidgeConfidenceFailureAt
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse R
          (allTimeTelescopingDelta delta (n + 1)) (n + 1) := by
    by_contra hgood
    exact (not_lt_of_ge (htrajectory n hgood)) hviolation
  unfold allTimeTelescopingScalarRidgeConfidenceFailureSet
  exact
    (mem_allTimeScheduledScalarRidgeConfidenceFailureSet_iff
      lambda thetaStar S
      (canonicalHistoryTrajectoryFeature actionFeature)
      canonicalHistoryTrajectoryResponse R
      (allTimeTelescopingDelta delta) trajectory).2
      ⟨n + 1, hfailure⟩

/--
Generated one-policy all-time successor-gap tail under the explicit scheduled
predictable-residual law.
-/
theorem
    measure_telescopingCanonicalHistoryTrajectoryAllTimeSuccGapViolationSet_le
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (comparator : Nat -> Fin K)
    (source : CanonicalScheduledPredictableScalarRidgeResidualLaw
      hK lambda thetaStar actionFeature R delta S environment) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
        (telescopingCanonicalHistoryTrajectoryAllTimeSuccGapViolationSet
          lambda thetaStar actionFeature R delta S comparator) <=
      ENNReal.ofReal delta := by
  calc
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
        (telescopingCanonicalHistoryTrajectoryAllTimeSuccGapViolationSet
          lambda thetaStar actionFeature R delta S comparator) <=
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
        (allTimeTelescopingScalarRidgeConfidenceFailureSet
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse R delta) := by
      exact measure_mono_ae
        (telescopingCanonicalHistoryTrajectoryAllTimeSuccGapViolationSet_subset_confidenceFailure_ae
          hK lambda hlambda thetaStar actionFeature R delta S
          environment comparator)
    _ <= ENNReal.ofReal delta :=
      measure_telescopingCanonicalHistoryTrajectory_allTimeConfidenceFailureSet_le
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S environment source

/--
Generated one-policy all-time confidence tail obtained directly from the
linear sub-Gaussian history-environment contract.
-/
theorem
    measure_telescopingCanonicalHistoryTrajectory_allTimeConfidenceFailureSet_le_of_linearSubgaussianEnvironment
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
        (allTimeTelescopingScalarRidgeConfidenceFailureSet
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse R delta) <=
      ENNReal.ofReal delta := by
  exact
    measure_telescopingCanonicalHistoryTrajectory_allTimeConfidenceFailureSet_le
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S environment
      (canonicalScheduledPredictableScalarRidgeResidualLaw_of_linearSubgaussianEnvironment
        hK lambda thetaStar actionFeature R delta S environment source)

/--
Generated one-policy all-time successor-gap tail obtained directly from the
linear sub-Gaussian history-environment contract.
-/
theorem
    measure_telescopingCanonicalHistoryTrajectoryAllTimeSuccGapViolationSet_le_of_linearSubgaussianEnvironment
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (comparator : Nat -> Fin K)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
        (telescopingCanonicalHistoryTrajectoryAllTimeSuccGapViolationSet
          lambda thetaStar actionFeature R delta S comparator) <=
      ENNReal.ofReal delta := by
  exact
    measure_telescopingCanonicalHistoryTrajectoryAllTimeSuccGapViolationSet_le
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S environment comparator
      (canonicalScheduledPredictableScalarRidgeResidualLaw_of_linearSubgaussianEnvironment
        hK lambda thetaStar actionFeature R delta S environment source)

end OFUL
end BanditRLProof
