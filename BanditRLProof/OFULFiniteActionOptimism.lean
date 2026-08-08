import BanditRLProof.OFULScalarRegularizationBias

/-!
# Finite-action optimism from the OFUL confidence ellipsoid

This module turns the compiled scalar-ridge confidence ellipsoid into a
finite-action optimistic selector and a one-step gap certificate.
-/

namespace BanditRLProof.OFUL

open MeasureTheory ProbabilityTheory Real Matrix WithLp Set
open scoped ENNReal NNReal ProbabilityTheory InnerProductSpace MatrixOrder

variable {Omega Feature Action : Type*}

/-- The inverse-Gram confidence width of one feature vector. -/
noncomputable def confidenceWidth
    [Fintype Feature] [DecidableEq Feature]
    (V : Matrix Feature Feature Real) (x : Feature -> Real) : Real :=
  Real.sqrt (dotProduct x (V⁻¹.mulVec x))

/-- Linear value of a feature vector under a parameter. -/
def linearValue
    [Fintype Feature]
    (theta x : Feature -> Real) : Real :=
  dotProduct theta x

/-- OFUL upper-confidence score `thetaHat dot x + beta * ||x||_(V⁻¹)`. -/
noncomputable def optimisticScore
    [Fintype Feature] [DecidableEq Feature]
    (thetaHat : Feature -> Real)
    (V : Matrix Feature Feature Real)
    (beta : Real) (x : Feature -> Real) : Real :=
  linearValue thetaHat x + beta * confidenceWidth V x

/-- A finite nonempty type admits a score-maximizing action. -/
noncomputable def finiteActionArgmax
    [Finite Action] [Nonempty Action]
    (score : Action -> Real) : Action :=
  Classical.choose (Finite.exists_max score)

/-- The finite-action argmax dominates every action score. -/
theorem finiteActionArgmax_spec
    [Finite Action] [Nonempty Action]
    (score : Action -> Real) (action : Action) :
    score action <= score (finiteActionArgmax score) :=
  Classical.choose_spec (Finite.exists_max score) action

/--
Weighted Cauchy-Schwarz: the ordinary dot product is controlled by the
`V`-norm and inverse-`V` confidence width.
-/
theorem abs_dotProduct_le_matrixNorm_mul_confidenceWidth
    [Fintype Feature] [DecidableEq Feature]
    (V : Matrix Feature Feature Real) (hV : V.PosDef)
    (error x : Feature -> Real) :
    |dotProduct error x| <=
      matrixNorm V error * confidenceWidth V x := by
  let inverseFeature : Feature -> Real := V⁻¹.mulVec x
  have hcancel : V.mulVec inverseFeature = x :=
    posDef_mulVec_nonsingInv_mulVec V hV x
  have hnorm (z : Feature -> Real) :
      matrixNorm V z =
        @norm (Feature -> Real) (V.toNormedAddCommGroup hV).toNorm z := by
    change Real.sqrt (dotProduct z (V.mulVec z)) =
      Real.sqrt (dotProduct (V.mulVec z) z)
    rw [dotProduct_comm]
  have hinverse_norm :
      matrixNorm V inverseFeature = confidenceWidth V x := by
    rw [matrixNorm, confidenceWidth, hcancel]
    exact congrArg Real.sqrt (dotProduct_comm inverseFeature x)
  letI := V.toNormedAddCommGroup hV
  letI := V.toInnerProductSpace hV.posSemidef
  have hinner :
      inner Real error inverseFeature =
        dotProduct error x := by
    change dotProduct (V.mulVec inverseFeature) error = dotProduct error x
    rw [hcancel, dotProduct_comm]
  have hcs :=
    @abs_real_inner_le_norm (Feature -> Real)
      (V.toNormedAddCommGroup hV).toSeminormedAddCommGroup
      (V.toInnerProductSpace hV.posSemidef)
      error inverseFeature
  rw [hinner] at hcs
  rw [← hnorm error, ← hnorm inverseFeature, hinverse_norm] at hcs
  exact hcs

/--
On a confidence ellipsoid, every true linear action value lies below its
upper-confidence score.
-/
theorem linearValue_le_optimisticScore_of_matrixNorm_sub_le
    [Fintype Feature] [DecidableEq Feature]
    (V : Matrix Feature Feature Real) (hV : V.PosDef)
    (thetaHat thetaStar : Feature -> Real) (beta : Real)
    (x : Feature -> Real)
    (hconfidence : matrixNorm V (thetaHat - thetaStar) <= beta) :
    linearValue thetaStar x <= optimisticScore thetaHat V beta x := by
  have hwidth_nonneg : 0 <= confidenceWidth V x := Real.sqrt_nonneg _
  have hdual :
      |dotProduct (thetaHat - thetaStar) x| <=
        beta * confidenceWidth V x :=
    (abs_dotProduct_le_matrixNorm_mul_confidenceWidth
      V hV (thetaHat - thetaStar) x).trans
      (mul_le_mul_of_nonneg_right hconfidence hwidth_nonneg)
  have hlower :
      -(beta * confidenceWidth V x) <=
        dotProduct (thetaHat - thetaStar) x :=
    (abs_le.mp hdual).1
  rw [sub_dotProduct] at hlower
  change dotProduct thetaStar x <=
    dotProduct thetaHat x + beta * confidenceWidth V x
  linarith

/--
On the same confidence ellipsoid, every upper-confidence score is at most
the true value plus twice its confidence bonus.
-/
theorem optimisticScore_le_linearValue_add_two_mul_bonus_of_matrixNorm_sub_le
    [Fintype Feature] [DecidableEq Feature]
    (V : Matrix Feature Feature Real) (hV : V.PosDef)
    (thetaHat thetaStar : Feature -> Real) (beta : Real)
    (x : Feature -> Real)
    (hconfidence : matrixNorm V (thetaHat - thetaStar) <= beta) :
    optimisticScore thetaHat V beta x <=
      linearValue thetaStar x + 2 * beta * confidenceWidth V x := by
  have hwidth_nonneg : 0 <= confidenceWidth V x := Real.sqrt_nonneg _
  have hdual :
      |dotProduct (thetaHat - thetaStar) x| <=
        beta * confidenceWidth V x :=
    (abs_dotProduct_le_matrixNorm_mul_confidenceWidth
      V hV (thetaHat - thetaStar) x).trans
      (mul_le_mul_of_nonneg_right hconfidence hwidth_nonneg)
  have hupper :
      dotProduct (thetaHat - thetaStar) x <=
        beta * confidenceWidth V x :=
    (abs_le.mp hdual).2
  rw [sub_dotProduct] at hupper
  change dotProduct thetaHat x + beta * confidenceWidth V x <=
    dotProduct thetaStar x + 2 * beta * confidenceWidth V x
  linarith

/-- The score-maximizing finite action for the OFUL upper-confidence score. -/
noncomputable def finiteActionOptimisticChoice
    [Finite Action] [Nonempty Action]
    [Fintype Feature] [DecidableEq Feature]
    (thetaHat : Feature -> Real)
    (V : Matrix Feature Feature Real)
    (beta : Real) (actionFeature : Action -> Feature -> Real) : Action :=
  finiteActionArgmax
    (fun action => optimisticScore thetaHat V beta (actionFeature action))

/-- The finite OFUL choice maximizes the optimistic score. -/
theorem finiteActionOptimisticChoice_score_max
    [Finite Action] [Nonempty Action]
    [Fintype Feature] [DecidableEq Feature]
    (thetaHat : Feature -> Real)
    (V : Matrix Feature Feature Real)
    (beta : Real) (actionFeature : Action -> Feature -> Real)
    (action : Action) :
    optimisticScore thetaHat V beta (actionFeature action) <=
      optimisticScore thetaHat V beta
        (actionFeature
          (finiteActionOptimisticChoice thetaHat V beta actionFeature)) := by
  exact finiteActionArgmax_spec
    (fun candidate =>
      optimisticScore thetaHat V beta (actionFeature candidate)) action

/--
On the confidence ellipsoid, the true value gap between any comparator and
the finite optimistic choice is at most twice the chosen action's bonus.
-/
theorem linearValue_sub_finiteActionOptimisticChoice_le_two_mul_bonus
    [Finite Action] [Nonempty Action]
    [Fintype Feature] [DecidableEq Feature]
    (V : Matrix Feature Feature Real) (hV : V.PosDef)
    (thetaHat thetaStar : Feature -> Real) (beta : Real)
    (actionFeature : Action -> Feature -> Real)
    (hconfidence : matrixNorm V (thetaHat - thetaStar) <= beta)
    (action : Action) :
    linearValue thetaStar (actionFeature action) -
        linearValue thetaStar
          (actionFeature
            (finiteActionOptimisticChoice thetaHat V beta actionFeature)) <=
      2 * beta *
        confidenceWidth V
          (actionFeature
            (finiteActionOptimisticChoice thetaHat V beta actionFeature)) := by
  let chosen :=
    finiteActionOptimisticChoice thetaHat V beta actionFeature
  have hoptimistic :
      linearValue thetaStar (actionFeature action) <=
        optimisticScore thetaHat V beta (actionFeature action) :=
    linearValue_le_optimisticScore_of_matrixNorm_sub_le
      V hV thetaHat thetaStar beta (actionFeature action) hconfidence
  have hmax :
      optimisticScore thetaHat V beta (actionFeature action) <=
        optimisticScore thetaHat V beta (actionFeature chosen) :=
    finiteActionOptimisticChoice_score_max
      thetaHat V beta actionFeature action
  have hchosen :
      optimisticScore thetaHat V beta (actionFeature chosen) <=
        linearValue thetaStar (actionFeature chosen) +
          2 * beta * confidenceWidth V (actionFeature chosen) :=
    optimisticScore_le_linearValue_add_two_mul_bonus_of_matrixNorm_sub_le
      V hV thetaHat thetaStar beta (actionFeature chosen) hconfidence
  dsimp only [chosen] at hmax hchosen
  linarith

/-- Scalar-regularized finite-horizon Gram matrix used by OFUL selection. -/
noncomputable def finiteHorizonScalarGram
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (n : Nat) (omega : Omega) : Matrix Feature Feature Real :=
  Matrix.scalar Feature lambda + finiteHorizonFeatureGram feature n omega

/--
Finite-action OFUL choice using the scalar-ridge estimate and the compiled
scalar confidence radius.
-/
noncomputable def finiteHorizonScalarOptimisticAction
    [Finite Action] [Nonempty Action]
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (candidateFeature : Omega -> Action -> Feature -> Real)
    (R delta S : Real) (n : Nat) (omega : Omega) : Action :=
  finiteActionOptimisticChoice
    (finiteHorizonRidgeEstimate
      (Matrix.scalar Feature lambda) feature response n omega)
    (finiteHorizonScalarGram lambda feature n omega)
    (finiteHorizonScalarConfidenceRadius
      feature R delta lambda S n omega)
    (candidateFeature omega)

/--
Pointwise finite-horizon optimism: on the scalar confidence ellipsoid, every
comparator's true linear value exceeds the selected value by at most twice
the selected confidence bonus.
-/
theorem finiteHorizonScalarOptimisticAction_gap_le
    [Finite Action] [Nonempty Action]
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real) (S : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (candidateFeature : Omega -> Action -> Feature -> Real)
    (R delta : Real) (n : Nat) (omega : Omega)
    (hconfidence :
      matrixNorm
          (finiteHorizonScalarGram lambda feature n omega)
          (finiteHorizonRidgeEstimate
              (Matrix.scalar Feature lambda) feature response n omega -
            thetaStar) <=
        finiteHorizonScalarConfidenceRadius
          feature R delta lambda S n omega)
    (action : Action) :
    linearValue thetaStar (candidateFeature omega action) -
        linearValue thetaStar
          (candidateFeature omega
            (finiteHorizonScalarOptimisticAction
              lambda feature response candidateFeature R delta S n omega)) <=
      2 *
        finiteHorizonScalarConfidenceRadius
          feature R delta lambda S n omega *
        confidenceWidth
          (finiteHorizonScalarGram lambda feature n omega)
          (candidateFeature omega
            (finiteHorizonScalarOptimisticAction
              lambda feature response candidateFeature R delta S n omega)) := by
  have hV :
      (finiteHorizonScalarGram lambda feature n omega).PosDef := by
    rw [finiteHorizonScalarGram]
    exact
      (scalarIdentity_posDef lambda hlambda).add_posSemidef
        (finiteHorizonFeatureGram_posSemidef feature n omega)
  simpa [finiteHorizonScalarOptimisticAction] using
    linearValue_sub_finiteActionOptimisticChoice_le_two_mul_bonus
      (finiteHorizonScalarGram lambda feature n omega) hV
      (finiteHorizonRidgeEstimate
        (Matrix.scalar Feature lambda) feature response n omega)
      thetaStar
      (finiteHorizonScalarConfidenceRadius
        feature R delta lambda S n omega)
      (candidateFeature omega) hconfidence action

/--
The event that some finite candidate action violates the one-step OFUL gap
certificate.
-/
noncomputable def finiteHorizonScalarOptimismViolationSet
    [Finite Action] [Nonempty Action]
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real) (thetaStar : Feature -> Real) (S : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (candidateFeature : Omega -> Action -> Feature -> Real)
    (R delta : Real) (n : Nat) : Set Omega :=
  {omega | ∃ action : Action,
    linearValue thetaStar (candidateFeature omega action) -
        linearValue thetaStar
          (candidateFeature omega
            (finiteHorizonScalarOptimisticAction
              lambda feature response candidateFeature R delta S n omega)) >
      2 *
        finiteHorizonScalarConfidenceRadius
          feature R delta lambda S n omega *
        confidenceWidth
          (finiteHorizonScalarGram lambda feature n omega)
          (candidateFeature omega
            (finiteHorizonScalarOptimisticAction
              lambda feature response candidateFeature R delta S n omega))}

/--
Finite-action OFUL optimism violation has probability at most `delta`.

No measurability of the candidate features or selected action is required:
the violation event is included pointwise in the already controlled scalar
confidence-ellipsoid bad event.
-/
theorem measure_finiteHorizonScalarOptimismViolationSet_le
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Finite Action] [Nonempty Action]
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real) (S : Real)
    (htheta : euclideanLength thetaStar <= S)
    (F : Filtration Nat mOmega)
    (feature : Nat -> Omega -> Feature -> Real)
    (response noise : Nat -> Omega -> Real)
    (candidateFeature : Omega -> Action -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (projectionBound : EuclideanSpace Real Feature -> Nat -> Real)
    (hfeature : forall i j,
      StronglyMeasurable[F i] (fun omega => feature i omega j))
    (hnoise : StronglyAdapted F (fun t omega =>
      match t with
      | 0 => 0
      | i + 1 => noise i omega))
    (hprojectionBound_nonneg : forall theta i,
      0 <= projectionBound theta i)
    (hprojectionBound : forall theta i omega,
      |dotProduct (WithLp.ofLp theta) (feature i omega)| <=
        projectionBound theta i)
    (n : Nat)
    (hsubGaussian : forall i, i < n ->
      HasCondSubgaussianMGF
        (F i) (F.le i) (noise i)
        (constantSquaredVarianceProxy R i) mu)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hresponse : forall omega i, i < n ->
      response i omega =
        dotProduct thetaStar (feature i omega) + noise i omega) :
    mu (finiteHorizonScalarOptimismViolationSet
        lambda thetaStar S feature response candidateFeature R delta n) <=
      ENNReal.ofReal delta := by
  calc
    _ <=
        mu {omega |
          matrixNorm
              (finiteHorizonScalarGram lambda feature n omega)
              (finiteHorizonRidgeEstimate
                  (Matrix.scalar Feature lambda) feature response n omega -
                thetaStar) >
            finiteHorizonScalarConfidenceRadius
              feature R delta lambda S n omega} := by
      apply measure_mono
      intro omega hviolation
      by_contra hnotBad
      have hconfidence :
          matrixNorm
              (finiteHorizonScalarGram lambda feature n omega)
              (finiteHorizonRidgeEstimate
                  (Matrix.scalar Feature lambda) feature response n omega -
                thetaStar) <=
            finiteHorizonScalarConfidenceRadius
              feature R delta lambda S n omega :=
        le_of_not_gt hnotBad
      obtain ⟨action, hgap⟩ := hviolation
      exact
        (not_lt_of_ge
          (finiteHorizonScalarOptimisticAction_gap_le
            lambda hlambda thetaStar S feature response candidateFeature
            R delta n omega hconfidence action)) hgap
    _ <= ENNReal.ofReal delta := by
      simpa [finiteHorizonScalarGram] using
        measure_finiteHorizonScalarRidgeEstimate_error_matrixNorm_gt_confidenceRadius_le
          mu lambda hlambda thetaStar S htheta F feature response noise R hR
          projectionBound hfeature hnoise hprojectionBound_nonneg
          hprojectionBound n hsubGaussian delta hdelta hdelta_one hresponse

end BanditRLProof.OFUL
