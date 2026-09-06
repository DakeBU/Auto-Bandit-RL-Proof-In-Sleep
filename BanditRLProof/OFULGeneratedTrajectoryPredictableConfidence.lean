import BanditRLProof.OFULGeneratedTrajectoryUniformConfidence
import BanditRLProof.HistoryFiltration

/-!
# Predictable canonical-trajectory confidence for OFUL

The actual canonical action coordinate is only almost surely equal to the
deterministic history selector.  This module constructs the pointwise
predictable selector feature under a strict-past filtration, proves its
almost-everywhere alignment with the actual selected feature, and transports
the compiled uniform confidence and successor-gap tails back to the actual
trajectory.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u

namespace BanditRLProof
namespace OFUL

/--
The canonical trajectory filtration strictly before the current coordinate.
Level zero is trivial, while level `n + 1` contains exactly coordinates
`0, ..., n`.
-/
def canonicalHistoryTrajectoryBeforeFiltration
    {K : Nat} :
    Filtration Nat
      (inferInstance : MeasurableSpace (Nat -> Fin K × Real)) where
  seq
    | 0 => ⊥
    | n + 1 =>
        Filtration.piLE (X := fun _ : Nat => Fin K × Real) n
  mono' := by
    intro i j hij
    cases i with
    | zero => exact bot_le
    | succ i =>
        cases j with
        | zero => exact (Nat.not_succ_le_zero i hij).elim
        | succ j =>
            exact
              (Filtration.piLE (X := fun _ : Nat => Fin K × Real)).mono
                (Nat.succ_le_succ_iff.mp hij)
  le' := by
    intro i
    cases i with
    | zero => exact bot_le
    | succ i =>
        exact
          (Filtration.piLE (X := fun _ : Nat => Fin K × Real)).le i

@[simp]
theorem canonicalHistoryTrajectoryBeforeFiltration_zero
    {K : Nat} :
    (canonicalHistoryTrajectoryBeforeFiltration (K := K) 0 :
      MeasurableSpace (Nat -> Fin K × Real)) = ⊥ := rfl

@[simp]
theorem canonicalHistoryTrajectoryBeforeFiltration_succ
    {K : Nat} (n : Nat) :
    (canonicalHistoryTrajectoryBeforeFiltration (K := K) (n + 1) :
      MeasurableSpace (Nat -> Fin K × Real)) =
      Filtration.piLE (X := fun _ : Nat => Fin K × Real) n := rfl

/-- The concrete scalar-ridge strict-fold selector is measurable in its history. -/
theorem measurable_finiteHistoryScalarRidgeOptimisticAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (n : Nat) :
    Measurable
      (finiteHistoryScalarRidgeOptimisticAction
        hK lambda actionFeature R delta S n) := by
  simpa only [finiteHistoryScalarRidgeOptimisticAction,
    finiteHistoryScalarRidgeOptimisticScore] using
    measurable_finiteHistoryOptimisticAction
      hK
      (finiteHistoryScalarRidgeEstimate lambda actionFeature)
      (finiteHistoryScalarRidgeDesign lambda actionFeature)
      (finiteHistoryScalarRidgeRadius actionFeature R delta lambda S)
      (finiteHistoryFixedActionFeature actionFeature)
      n
      (measurable_finiteHistoryScalarRidgeOptimisticScore
        lambda actionFeature R delta S n)

/--
Pointwise predictable feature used by scalar-ridge confidence.

At time zero it uses the deterministic initial arm.  At time `n + 1` it uses
the strict-fold selector evaluated only on coordinates through `n`.
-/
noncomputable def canonicalHistoryTrajectoryPredictableFeature
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) :
    Nat -> (Nat -> Fin K × Real) -> Feature -> Real
  | 0, _trajectory =>
      actionFeature ⟨0, hK⟩
  | n + 1, trajectory =>
      finiteHistoryScalarRidgeSelectedFeature
        hK lambda actionFeature R delta S n
        (Preorder.frestrictLe n trajectory)

/-- Every coordinate of the predictable feature is strict-past measurable. -/
theorem
    canonicalHistoryTrajectoryPredictableFeature_stronglyMeasurable
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (t : Nat) (j : Feature) :
    StronglyMeasurable[
      canonicalHistoryTrajectoryBeforeFiltration (K := K) t]
      (fun trajectory =>
        canonicalHistoryTrajectoryPredictableFeature
          hK lambda actionFeature R delta S t trajectory j) := by
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
            (finiteHistoryScalarRidgeOptimisticAction
              hK lambda actionFeature R delta S n) :=
        measurable_finiteHistoryScalarRidgeOptimisticAction
          hK lambda actionFeature R delta S n
      have hfeature :
          Measurable
            (fun history : History.FinitePairHistory (Fin K) Real n =>
              actionFeature
                (finiteHistoryScalarRidgeOptimisticAction
                  hK lambda actionFeature R delta S n history) j) :=
        (measurable_of_countable
          (fun action : Fin K => actionFeature action j)).comp hselector
      exact
        (hfeature.comp hprefix).stronglyMeasurable

/-- The initial canonical action of the concrete OFUL algorithm is its Dirac arm a.e. -/
theorem canonicalHistoryTrajectory_action_zero_ae_eq_initialArm
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment,
      Thompson.canonicalHistoryTrajectoryAction trajectory 0 = ⟨0, hK⟩ := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  let algorithm :=
    finiteHistoryScalarRidgeOptimisticAlgorithm
      hK lambda actionFeature R delta S
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
    simpa [algorithm, finiteHistoryScalarRidgeOptimisticAlgorithm,
      finiteHistoryOptimisticAlgorithm] using h
  have hdirac :
      ∀ᵐ action ∂Measure.dirac (⟨0, hK⟩ : Fin K),
        action = ⟨0, hK⟩ := by
    simp
  have hmap_ae :
      ∀ᵐ action ∂
          Measure.map
            (fun trajectory =>
              Thompson.canonicalHistoryTrajectoryAction trajectory 0)
            mu,
        action = ⟨0, hK⟩ := by
    rw [hmap]
    exact hdirac
  exact
    (ae_map_iff
      (Thompson.measurable_canonicalHistoryTrajectoryAction_apply 0).aemeasurable
      (by measurability)).mp hmap_ae

/-- Actual and pointwise predictable canonical features agree a.e. at each time. -/
theorem
    canonicalHistoryTrajectoryFeature_ae_eq_predictableFeature
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (t : Nat) :
    canonicalHistoryTrajectoryFeature actionFeature t =ᵐ[
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment]
      canonicalHistoryTrajectoryPredictableFeature
        hK lambda actionFeature R delta S t := by
  cases t with
  | zero =>
      filter_upwards [
        canonicalHistoryTrajectory_action_zero_ae_eq_initialArm
          hK lambda actionFeature R delta S environment] with
        trajectory htrajectory
      simp [canonicalHistoryTrajectoryFeature,
        canonicalHistoryTrajectoryPredictableFeature, htrajectory]
  | succ n =>
      simpa [canonicalHistoryTrajectoryFeature,
        canonicalHistoryTrajectoryPredictableFeature,
        History.finitePairHistoryOfTrace,
        Thompson.canonicalHistoryTrajectoryAction,
        Thompson.canonicalHistoryTrajectoryReward,
        Preorder.frestrictLe] using
        canonicalHistoryTrajectory_observedFeature_succ_ae_eq_finiteHistoryScalarRidgeSelectedFeature
          hK lambda actionFeature R delta S environment n

/-- Actual and predictable canonical features agree simultaneously at all times. -/
theorem
    canonicalHistoryTrajectoryFeature_ae_eq_predictableFeature_all
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment,
      ∀ t,
        canonicalHistoryTrajectoryFeature actionFeature t trajectory =
          canonicalHistoryTrajectoryPredictableFeature
            hK lambda actionFeature R delta S t trajectory := by
  rw [ae_all_iff]
  exact
    canonicalHistoryTrajectoryFeature_ae_eq_predictableFeature
      hK lambda actionFeature R delta S environment

/-- Canonical reward residual around the pointwise predictable linear response. -/
noncomputable def canonicalHistoryTrajectoryPredictableResidual
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (i : Nat) (trajectory : Nat -> Fin K × Real) : Real :=
  canonicalHistoryTrajectoryResponse i trajectory -
    dotProduct thetaStar
      (canonicalHistoryTrajectoryPredictableFeature
        hK lambda actionFeature R delta S i trajectory)

/-- The canonical reward coordinate at time `i` is measurable at level `i + 1`. -/
theorem measurable_canonicalHistoryTrajectoryResponse_before_succ
    {K : Nat} (i : Nat) :
    @Measurable (Nat -> Fin K × Real) Real
      (canonicalHistoryTrajectoryBeforeFiltration (K := K) (i + 1))
      inferInstance
      (canonicalHistoryTrajectoryResponse i) := by
  let F := canonicalHistoryTrajectoryBeforeFiltration (K := K)
  have hprefix :
      @Measurable (Nat -> Fin K × Real)
        ((j : Finset.Iic i) -> Fin K × Real)
        (F (i + 1)) inferInstance
        (Preorder.frestrictLe i) := by
    rw [canonicalHistoryTrajectoryBeforeFiltration_succ,
      Filtration.piLE_eq_comap_frestrictLe]
    exact Measurable.of_comap_le le_rfl
  let last : Finset.Iic i := ⟨i, Finset.mem_Iic.mpr le_rfl⟩
  have heval :
      Measurable
        (fun history : (j : Finset.Iic i) -> Fin K × Real =>
          (history last).2) :=
    measurable_snd.comp (measurable_pi_apply last)
  simpa [F, last, canonicalHistoryTrajectoryResponse] using
    heval.comp hprefix

/-- The zero-initialized predictable residual process is strongly adapted. -/
theorem canonicalHistoryTrajectoryPredictableResidual_stronglyAdapted
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) :
    StronglyAdapted
      (canonicalHistoryTrajectoryBeforeFiltration (K := K))
      (fun t trajectory =>
        match t with
        | 0 => 0
        | i + 1 =>
            canonicalHistoryTrajectoryPredictableResidual
              hK lambda thetaStar actionFeature R delta S i trajectory) := by
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
              canonicalHistoryTrajectoryPredictableFeature
                hK lambda actionFeature R delta S i trajectory j) := by
        intro j
        exact
          (canonicalHistoryTrajectoryPredictableFeature_stronglyMeasurable
            hK lambda actionFeature R delta S i j).mono
            (F.mono (Nat.le_succ i))
      have hdot :
          StronglyMeasurable[F (i + 1)]
            (fun trajectory =>
              dotProduct thetaStar
                (canonicalHistoryTrajectoryPredictableFeature
                  hK lambda actionFeature R delta S i trajectory)) := by
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
      simpa [F, canonicalHistoryTrajectoryPredictableResidual] using
        hresponse.sub hdot

/-- Maximum absolute projection over the finite arm set. -/
noncomputable def finiteActionProjectionBound
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (hK : 0 < K)
    (actionFeature : Fin K -> Feature -> Real)
    (theta : EuclideanSpace Real Feature) : Real := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  exact
    Finset.univ.sup' Finset.univ_nonempty
      (fun action =>
        |dotProduct (WithLp.ofLp theta) (actionFeature action)|)

theorem finiteActionProjectionBound_nonneg
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (hK : 0 < K)
    (actionFeature : Fin K -> Feature -> Real)
    (theta : EuclideanSpace Real Feature) :
    0 <= finiteActionProjectionBound hK actionFeature theta := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  exact
    (abs_nonneg
      (dotProduct (WithLp.ofLp theta)
        (actionFeature (⟨0, hK⟩ : Fin K)))).trans
      (by
        simpa [finiteActionProjectionBound] using
          (Finset.le_sup'
            (s := (Finset.univ : Finset (Fin K)))
            (f := fun action =>
              |dotProduct (WithLp.ofLp theta) (actionFeature action)|)
            (Finset.mem_univ (⟨0, hK⟩ : Fin K))))

theorem predictableFeature_projection_le_finiteActionProjectionBound
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (theta : EuclideanSpace Real Feature)
    (i : Nat) (trajectory : Nat -> Fin K × Real) :
    |dotProduct (WithLp.ofLp theta)
        (canonicalHistoryTrajectoryPredictableFeature
          hK lambda actionFeature R delta S i trajectory)| <=
      finiteActionProjectionBound hK actionFeature theta := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  cases i with
  | zero =>
      simpa [canonicalHistoryTrajectoryPredictableFeature,
        finiteActionProjectionBound] using
        (Finset.le_sup'
          (s := (Finset.univ : Finset (Fin K)))
          (f := fun action =>
            |dotProduct (WithLp.ofLp theta) (actionFeature action)|)
          (Finset.mem_univ (⟨0, hK⟩ : Fin K)))
  | succ n =>
      simpa [canonicalHistoryTrajectoryPredictableFeature,
        finiteHistoryScalarRidgeSelectedFeature,
        finiteActionProjectionBound] using
        (Finset.le_sup'
          (s := (Finset.univ : Finset (Fin K)))
          (f := fun action =>
            |dotProduct (WithLp.ofLp theta) (actionFeature action)|)
          (Finset.mem_univ
            (finiteHistoryScalarRidgeOptimisticAction
              hK lambda actionFeature R delta S n
              (Preorder.frestrictLe n trajectory))))

/--
The remaining stochastic law for predictable canonical confidence.

Measurability, adaptedness, deterministic finite-arm projection bounds, and
the pointwise response identity are derived by this module.  A concrete
environment producer therefore only needs the parameter norm and the
strict-past conditional MGF of the canonical predictable residual.
-/
structure CanonicalPredictableScalarRidgeResidualLaw
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R algorithmDelta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) : Prop where
  theta_norm_le : euclideanLength thetaStar <= S
  residual_hasCondSubgaussianMGF : forall i, i < horizon ->
    ProbabilityTheory.HasCondSubgaussianMGF
      (canonicalHistoryTrajectoryBeforeFiltration (K := K) i)
      ((canonicalHistoryTrajectoryBeforeFiltration (K := K)).le i)
      (canonicalHistoryTrajectoryPredictableResidual
        hK lambda thetaStar actionFeature R algorithmDelta S i)
      (constantSquaredVarianceProxy R i)
      (Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R algorithmDelta S)
        environment)

/-- Pointwise feature equality preserves every fixed-time scalar-ridge event. -/
theorem mem_scalarRidgeConfidenceFailureAt_iff_of_feature_eq
    {Omega : Type*} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (S : Real)
    (feature feature' : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (R delta : Real)
    (n : Nat) (omega : Omega)
    (hfeature : forall i, feature i omega = feature' i omega) :
    omega ∈
        scalarRidgeConfidenceFailureAt
          lambda thetaStar S feature response R delta n ↔
      omega ∈
        scalarRidgeConfidenceFailureAt
          lambda thetaStar S feature' response R delta n := by
  have hgram :
      finiteHorizonFeatureGram feature n omega =
        finiteHorizonFeatureGram feature' n omega := by
    ext j k
    simp only [finiteHorizonFeatureGram, prefixFeatureGram]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hfeature i]
  have hresponseVector :
      finiteHorizonResponseVector feature response n omega =
        finiteHorizonResponseVector feature' response n omega := by
    ext j
    simp only [finiteHorizonResponseVector]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hfeature i]
  simp only [scalarRidgeConfidenceFailureAt, Set.mem_setOf_eq,
    finiteHorizonScalarConfidenceRadius, finiteHorizonConfidenceRadius,
    finiteHorizonConfidenceThreshold, finiteHorizonRidgeEstimate]
  rw [hgram, hresponseVector]

/-- Pointwise feature equality preserves the finite-window uniform failure event. -/
theorem mem_finiteHorizonUniformScalarRidgeConfidenceFailureSet_iff_of_feature_eq
    {Omega : Type*} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (S : Real)
    (feature feature' : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (R delta : Real)
    (horizon : Nat) (omega : Omega)
    (hfeature : forall i, feature i omega = feature' i omega) :
    omega ∈
        finiteHorizonUniformScalarRidgeConfidenceFailureSet
          lambda thetaStar S feature response R delta horizon ↔
      omega ∈
        finiteHorizonUniformScalarRidgeConfidenceFailureSet
          lambda thetaStar S feature' response R delta horizon := by
  simp only [finiteHorizonUniformScalarRidgeConfidenceFailureSet]
  rw [
    mem_finiteHorizonScheduledScalarRidgeConfidenceFailureSet_iff,
    mem_finiteHorizonScheduledScalarRidgeConfidenceFailureSet_iff]
  constructor
  · rintro ⟨n, hn, hfailure⟩
    exact ⟨n, hn,
      (mem_scalarRidgeConfidenceFailureAt_iff_of_feature_eq
        lambda thetaStar S feature feature' response R
        (delta / ((horizon + 1 : Nat) : Real)) n omega hfeature).mp
        hfailure⟩
  · rintro ⟨n, hn, hfailure⟩
    exact ⟨n, hn,
      (mem_scalarRidgeConfidenceFailureAt_iff_of_feature_eq
        lambda thetaStar S feature feature' response R
        (delta / ((horizon + 1 : Nat) : Real)) n omega hfeature).mpr
        hfailure⟩

/--
Uniform scalar-ridge confidence on the actual canonical selected features,
derived from only the predictable residual conditional law.
-/
theorem
    measure_canonicalHistoryTrajectory_uniformScalarRidgeConfidenceFailureSet_le_of_predictableResidualLaw
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
    (horizon : Nat)
    (source : CanonicalPredictableScalarRidgeResidualLaw
      hK lambda thetaStar actionFeature R
        (delta / ((horizon + 1 : Nat) : Real)) S
      environment horizon) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R
            (delta / ((horizon + 1 : Nat) : Real)) S)
        environment
        (finiteHorizonUniformScalarRidgeConfidenceFailureSet
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse
          R delta horizon) <=
      ENNReal.ofReal delta := by
  let algorithmDelta := delta / ((horizon + 1 : Nat) : Real)
  let algorithm :=
    finiteHistoryScalarRidgeOptimisticAlgorithm
      hK lambda actionFeature R algorithmDelta S
  let mu := Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
  let F := canonicalHistoryTrajectoryBeforeFiltration (K := K)
  let predictableFeature :=
    canonicalHistoryTrajectoryPredictableFeature
      hK lambda actionFeature R algorithmDelta S
  let residual :=
    canonicalHistoryTrajectoryPredictableResidual
      hK lambda thetaStar actionFeature R algorithmDelta S
  have hpredictable :
      mu
          (finiteHorizonUniformScalarRidgeConfidenceFailureSet
            lambda thetaStar S predictableFeature
            canonicalHistoryTrajectoryResponse R delta horizon) <=
        ENNReal.ofReal delta := by
    apply
      measure_finiteHorizonUniformScalarRidgeConfidenceFailureSet_le
        mu lambda hlambda thetaStar S source.theta_norm_le F
        predictableFeature canonicalHistoryTrajectoryResponse residual
        R hR
        (fun theta _i =>
          finiteActionProjectionBound hK actionFeature theta)
    · intro i j
      exact
        canonicalHistoryTrajectoryPredictableFeature_stronglyMeasurable
          hK lambda actionFeature R algorithmDelta S i j
    · exact
        canonicalHistoryTrajectoryPredictableResidual_stronglyAdapted
          hK lambda thetaStar actionFeature R algorithmDelta S
    · intro theta i
      exact finiteActionProjectionBound_nonneg hK actionFeature theta
    · intro theta i trajectory
      exact
        predictableFeature_projection_le_finiteActionProjectionBound
          hK lambda actionFeature R algorithmDelta S theta i trajectory
    · intro i hi
      exact source.residual_hasCondSubgaussianMGF i hi
    · intro trajectory i _hi
      simp [residual, predictableFeature,
        canonicalHistoryTrajectoryPredictableResidual]
    · exact hdelta
    · exact hdelta_one
  have hevents :
      ∀ᵐ trajectory ∂mu,
        trajectory ∈
            finiteHorizonUniformScalarRidgeConfidenceFailureSet
              lambda thetaStar S
              (canonicalHistoryTrajectoryFeature actionFeature)
              canonicalHistoryTrajectoryResponse R delta horizon ↔
          trajectory ∈
            finiteHorizonUniformScalarRidgeConfidenceFailureSet
              lambda thetaStar S predictableFeature
              canonicalHistoryTrajectoryResponse R delta horizon := by
    filter_upwards [
      canonicalHistoryTrajectoryFeature_ae_eq_predictableFeature_all
        hK lambda actionFeature R algorithmDelta S environment] with
      trajectory htrajectory
    exact
      mem_finiteHorizonUniformScalarRidgeConfidenceFailureSet_iff_of_feature_eq
        lambda thetaStar S
        (canonicalHistoryTrajectoryFeature actionFeature)
        predictableFeature canonicalHistoryTrajectoryResponse
        R delta horizon trajectory htrajectory
  calc
    mu
        (finiteHorizonUniformScalarRidgeConfidenceFailureSet
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse R delta horizon) =
        mu
          (finiteHorizonUniformScalarRidgeConfidenceFailureSet
            lambda thetaStar S predictableFeature
            canonicalHistoryTrajectoryResponse R delta horizon) :=
      measure_congr (hevents.mono fun _ h => propext h)
    _ <= ENNReal.ofReal delta := hpredictable

/--
Canonical successor-gap tail derived from the strict-past predictable residual
law.  Unlike the earlier source theorem, no pointwise measurability of the
actual selected feature is assumed.
-/
theorem
    measure_canonicalHistoryTrajectorySumRangeSuccGapViolationSet_le_of_predictableResidualLaw
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
    (horizon : Nat)
    (comparator : Nat -> Fin K)
    (source : CanonicalPredictableScalarRidgeResidualLaw
      hK lambda thetaStar actionFeature R
        (delta / ((horizon + 1 : Nat) : Real)) S
      environment horizon) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R
            (delta / ((horizon + 1 : Nat) : Real)) S)
        environment
        (canonicalHistoryTrajectorySumRangeSuccGapViolationSet
          lambda thetaStar actionFeature R delta S horizon comparator) <=
      ENNReal.ofReal delta := by
  let algorithm :=
    finiteHistoryScalarRidgeOptimisticAlgorithm
      hK lambda actionFeature R
        (delta / ((horizon + 1 : Nat) : Real)) S
  let mu := Thompson.canonicalHistoryTrajectoryMeasure algorithm environment
  let failureSet :=
    finiteHorizonUniformScalarRidgeConfidenceFailureSet
      lambda thetaStar S
      (canonicalHistoryTrajectoryFeature actionFeature)
      canonicalHistoryTrajectoryResponse
      R delta horizon
  have hfailure : mu failureSet <= ENNReal.ofReal delta := by
    exact
      measure_canonicalHistoryTrajectory_uniformScalarRidgeConfidenceFailureSet_le_of_predictableResidualLaw
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S environment horizon source
  have hgap :=
    canonicalHistoryTrajectory_sum_range_succ_gap_le_on_uniformConfidence
      hK lambda hlambda thetaStar actionFeature R delta S
      environment horizon comparator
  calc
    mu
        (canonicalHistoryTrajectorySumRangeSuccGapViolationSet
          lambda thetaStar actionFeature R delta S horizon comparator) <=
        mu failureSet := by
      apply measure_mono_ae
      filter_upwards [hgap] with trajectory htrajectory
      intro hviolation
      by_contra hnotFailure
      exact (not_lt_of_ge (htrajectory hnotFailure)) hviolation
    _ <= ENNReal.ofReal delta := hfailure

end OFUL
end BanditRLProof
