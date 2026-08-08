import BanditRLProof.OFULMeasurableRecursiveSelection

/-!
# Concrete finite-history scalar-ridge OFUL selection

This module reconstructs the standard scalar-ridge OFUL state from an
inclusive finite action/Real-reward history.  It proves the complete
finite-dimensional measurability chain and instantiates the measurable
recursive selector without a caller-supplied score-measurability premise.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v

namespace BanditRLProof
namespace OFUL

/-- A determinant is measurable when every random matrix entry is measurable. -/
theorem measurable_matrix_det_of_apply
    {Omega Index : Type*} [MeasurableSpace Omega]
    [Fintype Index] [DecidableEq Index]
    (A : Omega -> Matrix Index Index Real)
    (hA : forall i j, Measurable (fun omega => A omega i j)) :
    Measurable (fun omega => Matrix.det (A omega)) := by
  classical
  simp_rw [Matrix.det_apply']
  refine Finset.measurable_sum _ ?_
  intro sigma _hsigma
  exact measurable_const.mul <|
    Finset.measurable_prod _ fun i _hi => hA (sigma i) i

/-- Every adjugate entry is measurable under coordinatewise matrix measurability. -/
theorem measurable_matrix_adjugate_apply_of_apply
    {Omega Index : Type*} [MeasurableSpace Omega]
    [Fintype Index] [DecidableEq Index]
    (A : Omega -> Matrix Index Index Real)
    (hA : forall i j, Measurable (fun omega => A omega i j))
    (i j : Index) :
    Measurable (fun omega => Matrix.adjugate (A omega) i j) := by
  rw [show (fun omega => Matrix.adjugate (A omega) i j) =
      fun omega => Matrix.det ((A omega).updateRow j (Pi.single i 1)) by
    funext omega
    exact Matrix.adjugate_apply (A omega) i j]
  apply measurable_matrix_det_of_apply
  intro row col
  by_cases hrow : row = j
  · subst row
    simpa using measurable_const
  · simpa [Matrix.updateRow_apply, hrow] using hA row col

/--
Every entry of Mathlib's nonsingular inverse is measurable.  The proof uses
the determinant/adjugate formula, including its zero-at-singular convention.
-/
theorem measurable_matrix_nonsingInv_apply_of_apply
    {Omega Index : Type*} [MeasurableSpace Omega]
    [Fintype Index] [DecidableEq Index]
    (A : Omega -> Matrix Index Index Real)
    (hA : forall i j, Measurable (fun omega => A omega i j))
    (i j : Index) :
    Measurable (fun omega => (A omega)⁻¹ i j) := by
  have hdet : Measurable (fun omega => Matrix.det (A omega)) :=
    measurable_matrix_det_of_apply A hA
  have hadjugate :
      Measurable (fun omega => Matrix.adjugate (A omega) i j) :=
    measurable_matrix_adjugate_apply_of_apply A hA i j
  simpa only [Matrix.inv_def, Pi.smul_apply, smul_eq_mul,
    Ring.inverse_eq_inv] using hdet.inv.mul hadjugate

/-- A random matrix-vector product is coordinatewise measurable. -/
theorem measurable_matrix_mulVec_apply_of_apply
    {Omega Index : Type*} [MeasurableSpace Omega] [Fintype Index]
    (A : Omega -> Matrix Index Index Real)
    (x : Omega -> Index -> Real)
    (hA : forall i j, Measurable (fun omega => A omega i j))
    (hx : forall i, Measurable (fun omega => x omega i))
    (i : Index) :
    Measurable (fun omega => (A omega).mulVec (x omega) i) := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _hj => (hA i j).mul (hx j)

/-- A random finite dot product is measurable coordinatewise. -/
theorem measurable_dotProduct_of_apply
    {Omega Index : Type*} [MeasurableSpace Omega] [Fintype Index]
    (x y : Omega -> Index -> Real)
    (hx : forall i, Measurable (fun omega => x omega i))
    (hy : forall i, Measurable (fun omega => y omega i)) :
    Measurable (fun omega => dotProduct (x omega) (y omega)) := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun i _hi => (hx i).mul (hy i)

/-- The OFUL confidence width is measurable from matrix and feature coordinates. -/
theorem measurable_confidenceWidth_of_apply
    {Omega Feature : Type*} [MeasurableSpace Omega]
    [Fintype Feature] [DecidableEq Feature]
    (V : Omega -> Matrix Feature Feature Real)
    (x : Omega -> Feature -> Real)
    (hV : forall i j, Measurable (fun omega => V omega i j))
    (hx : forall i, Measurable (fun omega => x omega i)) :
    Measurable (fun omega => confidenceWidth (V omega) (x omega)) := by
  unfold confidenceWidth
  apply Measurable.sqrt
  apply measurable_dotProduct_of_apply x
    (fun omega => (V omega)⁻¹.mulVec (x omega)) hx
  intro i
  apply measurable_matrix_mulVec_apply_of_apply
  · intro row col
    exact measurable_matrix_nonsingInv_apply_of_apply V hV row col
  · exact hx

/-- The OFUL optimistic score is measurable from its scalar coordinates. -/
theorem measurable_optimisticScore_of_apply
    {Omega Feature : Type*} [MeasurableSpace Omega]
    [Fintype Feature] [DecidableEq Feature]
    (thetaHat : Omega -> Feature -> Real)
    (V : Omega -> Matrix Feature Feature Real)
    (beta : Omega -> Real)
    (x : Omega -> Feature -> Real)
    (hthetaHat : forall i,
      Measurable (fun omega => thetaHat omega i))
    (hV : forall i j, Measurable (fun omega => V omega i j))
    (hbeta : Measurable beta)
    (hx : forall i, Measurable (fun omega => x omega i)) :
    Measurable (fun omega =>
      optimisticScore (thetaHat omega) (V omega) (beta omega) (x omega)) := by
  unfold optimisticScore linearValue
  exact
    (measurable_dotProduct_of_apply thetaHat x hthetaHat hx).add
      (hbeta.mul (measurable_confidenceWidth_of_apply V x hV hx))

/-- Entries of a finite-horizon feature Gram are measurable. -/
theorem measurable_finiteHorizonFeatureGram_apply
    {Omega Feature : Type*} [MeasurableSpace Omega]
    (feature : Nat -> Omega -> Feature -> Real)
    (hfeature : forall t i,
      Measurable (fun omega => feature t omega i))
    (n : Nat) (i j : Feature) :
    Measurable (fun omega =>
      finiteHorizonFeatureGram feature n omega i j) := by
  unfold finiteHorizonFeatureGram prefixFeatureGram
  exact Finset.measurable_sum _ fun t _ht =>
    (hfeature t i).mul (hfeature t j)

/-- Coordinates of the finite-horizon response vector are measurable. -/
theorem measurable_finiteHorizonResponseVector_apply
    {Omega Feature : Type*} [MeasurableSpace Omega]
    [Fintype Feature]
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (hfeature : forall t i,
      Measurable (fun omega => feature t omega i))
    (hresponse : forall t, Measurable (response t))
    (n : Nat) (i : Feature) :
    Measurable (fun omega =>
      finiteHorizonResponseVector feature response n omega i) := by
  unfold finiteHorizonResponseVector
  exact Finset.measurable_sum _ fun t _ht =>
    (hfeature t i).mul (hresponse t)

/-- Every coordinate of the finite-horizon ridge estimate is measurable. -/
theorem measurable_finiteHorizonRidgeEstimate_apply
    {Omega Feature : Type*} [MeasurableSpace Omega]
    [Fintype Feature] [DecidableEq Feature]
    (V0 : Matrix Feature Feature Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (response : Nat -> Omega -> Real)
    (hfeature : forall t i,
      Measurable (fun omega => feature t omega i))
    (hresponse : forall t, Measurable (response t))
    (n : Nat) (i : Feature) :
    Measurable (fun omega =>
      finiteHorizonRidgeEstimate V0 feature response n omega i) := by
  unfold finiteHorizonRidgeEstimate
  apply measurable_matrix_mulVec_apply_of_apply
  · intro row col
    apply measurable_matrix_nonsingInv_apply_of_apply
    intro r c
    exact measurable_const.add
      (measurable_finiteHorizonFeatureGram_apply
        feature hfeature n r c)
  · intro j
    exact measurable_finiteHorizonResponseVector_apply
      feature response hfeature hresponse n j

/-- The scalar-ridge finite-horizon confidence radius is measurable. -/
theorem measurable_finiteHorizonScalarConfidenceRadius
    {Omega Feature : Type*} [MeasurableSpace Omega]
    [Fintype Feature] [DecidableEq Feature]
    (feature : Nat -> Omega -> Feature -> Real)
    (hfeature : forall t i,
      Measurable (fun omega => feature t omega i))
    (R delta lambda S : Real) (n : Nat) :
    Measurable (finiteHorizonScalarConfidenceRadius
      feature R delta lambda S n) := by
  have hmatrix : forall i j,
      Measurable (fun omega =>
        (Matrix.scalar Feature lambda +
          finiteHorizonFeatureGram feature n omega) i j) := by
    intro i j
    exact measurable_const.add
      (measurable_finiteHorizonFeatureGram_apply
        feature hfeature n i j)
  have hdet : Measurable (fun omega =>
      Matrix.det
        (Matrix.scalar Feature lambda +
          finiteHorizonFeatureGram feature n omega)) :=
    measurable_matrix_det_of_apply _ hmatrix
  unfold finiteHorizonScalarConfidenceRadius
    finiteHorizonConfidenceRadius finiteHorizonConfidenceThreshold
  exact
    ((measurable_const.mul
      (((hdet.div_const _).sqrt.div_const delta).log)).sqrt).add_const _

/-- Feature observed at a history coordinate, with zero outside the prefix. -/
noncomputable def finiteHistoryObservedFeature
    {K : Nat} {Feature : Type u}
    (actionFeature : Fin K -> Feature -> Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n)
    (t : Nat) : Feature -> Real :=
  if ht : t <= n then
    actionFeature (history ⟨t, Finset.mem_Iic.mpr ht⟩).1
  else
    0

/-- Reward observed at a history coordinate, with zero outside the prefix. -/
noncomputable def finiteHistoryObservedResponse
    {K : Nat}
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n)
    (t : Nat) : Real :=
  if ht : t <= n then
    (history ⟨t, Finset.mem_Iic.mpr ht⟩).2
  else
    0

/-- Every coordinate of the history-observed feature process is measurable. -/
theorem measurable_finiteHistoryObservedFeature_apply
    {K : Nat} {Feature : Type u}
    (actionFeature : Fin K -> Feature -> Real)
    (n t : Nat) (i : Feature) :
    Measurable (fun history : History.FinitePairHistory (Fin K) Real n =>
      finiteHistoryObservedFeature actionFeature n history t i) := by
  classical
  by_cases ht : t <= n
  · simp only [finiteHistoryObservedFeature, dif_pos ht]
    exact
      (measurable_of_countable (fun action : Fin K => actionFeature action i)).comp
        (measurable_fst.comp
          (measurable_pi_apply
            (⟨t, Finset.mem_Iic.mpr ht⟩ : Finset.Iic n)))
  · simp [finiteHistoryObservedFeature, ht]

/-- The history-observed response process is measurable. -/
theorem measurable_finiteHistoryObservedResponse
    {K : Nat} (n t : Nat) :
    Measurable (fun history : History.FinitePairHistory (Fin K) Real n =>
      finiteHistoryObservedResponse n history t) := by
  classical
  by_cases ht : t <= n
  · simp only [finiteHistoryObservedResponse, dif_pos ht]
    exact measurable_snd.comp
      (measurable_pi_apply
        (⟨t, Finset.mem_Iic.mpr ht⟩ : Finset.Iic n))
  · simp [finiteHistoryObservedResponse, ht]

/-- Scalar-ridge estimate reconstructed from the inclusive finite history. -/
noncomputable def finiteHistoryScalarRidgeEstimate
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n) :
    Feature -> Real :=
  finiteHorizonRidgeEstimate
    (Matrix.scalar Feature lambda)
    (fun t historyValue =>
      finiteHistoryObservedFeature actionFeature n historyValue t)
    (fun t historyValue =>
      finiteHistoryObservedResponse n historyValue t)
    (n + 1) history

/-- Scalar-ridge design matrix reconstructed from the inclusive finite history. -/
noncomputable def finiteHistoryScalarRidgeDesign
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n) :
    Matrix Feature Feature Real :=
  Matrix.scalar Feature lambda +
    finiteHorizonFeatureGram
      (fun t historyValue =>
        finiteHistoryObservedFeature actionFeature n historyValue t)
      (n + 1) history

/-- Scalar confidence radius reconstructed from the inclusive finite history. -/
noncomputable def finiteHistoryScalarRidgeRadius
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (actionFeature : Fin K -> Feature -> Real)
    (R delta lambda S : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n) :
    Real :=
  finiteHorizonScalarConfidenceRadius
    (fun t historyValue =>
      finiteHistoryObservedFeature actionFeature n historyValue t)
    R delta lambda S (n + 1) history

/-- The fixed feature of an arm, exposed on the finite-history component API. -/
def finiteHistoryFixedActionFeature
    {K : Nat} {Feature : Type u}
    (actionFeature : Fin K -> Feature -> Real)
    (n : Nat) (_history : History.FinitePairHistory (Fin K) Real n)
    (action : Fin K) : Feature -> Real :=
  actionFeature action

/-- Concrete scalar-ridge OFUL score computed from an inclusive finite history. -/
noncomputable def finiteHistoryScalarRidgeOptimisticScore
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n)
    (action : Fin K) : Real :=
  finiteHistoryOptimisticScore
    (finiteHistoryScalarRidgeEstimate lambda actionFeature)
    (finiteHistoryScalarRidgeDesign lambda actionFeature)
    (finiteHistoryScalarRidgeRadius actionFeature R delta lambda S)
    (finiteHistoryFixedActionFeature actionFeature)
    n history action

/--
Every fixed-arm concrete scalar-ridge score is measurable.  In particular,
callers do not need to supply a score-measurability premise.
-/
theorem measurable_finiteHistoryScalarRidgeOptimisticScore
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) (n : Nat) (action : Fin K) :
    Measurable (fun history : History.FinitePairHistory (Fin K) Real n =>
      finiteHistoryScalarRidgeOptimisticScore
        lambda actionFeature R delta S n history action) := by
  unfold finiteHistoryScalarRidgeOptimisticScore
    finiteHistoryOptimisticScore
    finiteHistoryScalarRidgeEstimate
    finiteHistoryScalarRidgeDesign
    finiteHistoryScalarRidgeRadius
    finiteHistoryFixedActionFeature
  apply measurable_optimisticScore_of_apply
  · intro i
    exact measurable_finiteHorizonRidgeEstimate_apply
      (Matrix.scalar Feature lambda)
      (fun t historyValue =>
        finiteHistoryObservedFeature actionFeature n historyValue t)
      (fun t historyValue =>
        finiteHistoryObservedResponse n historyValue t)
      (fun t i =>
        measurable_finiteHistoryObservedFeature_apply
          actionFeature n t i)
      (measurable_finiteHistoryObservedResponse n)
      (n + 1) i
  · intro i j
    exact measurable_const.add
      (measurable_finiteHorizonFeatureGram_apply
        (fun t historyValue =>
          finiteHistoryObservedFeature actionFeature n historyValue t)
        (fun t i =>
          measurable_finiteHistoryObservedFeature_apply
            actionFeature n t i)
        (n + 1) i j)
  · exact measurable_finiteHorizonScalarConfidenceRadius
      (fun t historyValue =>
        finiteHistoryObservedFeature actionFeature n historyValue t)
      (fun t i =>
        measurable_finiteHistoryObservedFeature_apply
          actionFeature n t i)
      R delta lambda S (n + 1)
  · intro i
    exact measurable_const

/-- Deterministic score-maximizing arm for the concrete scalar-ridge state. -/
noncomputable def finiteHistoryScalarRidgeOptimisticAction
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n) :
    Fin K :=
  finiteHistoryOptimisticAction
    hK
    (finiteHistoryScalarRidgeEstimate lambda actionFeature)
    (finiteHistoryScalarRidgeDesign lambda actionFeature)
    (finiteHistoryScalarRidgeRadius actionFeature R delta lambda S)
    (finiteHistoryFixedActionFeature actionFeature)
    n history

/-- The concrete finite-history selector maximizes its scalar-ridge score. -/
theorem finiteHistoryScalarRidgeOptimisticAction_score_max
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n)
    (action : Fin K) :
    finiteHistoryScalarRidgeOptimisticScore
        lambda actionFeature R delta S n history action <=
      finiteHistoryScalarRidgeOptimisticScore
        lambda actionFeature R delta S n history
        (finiteHistoryScalarRidgeOptimisticAction
          hK lambda actionFeature R delta S n history) := by
  exact finiteHistoryOptimisticAction_score_max
    hK
    (finiteHistoryScalarRidgeEstimate lambda actionFeature)
    (finiteHistoryScalarRidgeDesign lambda actionFeature)
    (finiteHistoryScalarRidgeRadius actionFeature R delta lambda S)
    (finiteHistoryFixedActionFeature actionFeature)
    n history action

/--
Concrete measurable history algorithm obtained from the reconstructed
scalar-ridge state, with score measurability discharged internally.
-/
noncomputable def finiteHistoryScalarRidgeOptimisticAlgorithm
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) :
    Thompson.HistoryAlgorithm (Fin K) Real :=
  finiteHistoryOptimisticAlgorithm
    hK
    (finiteHistoryScalarRidgeEstimate lambda actionFeature)
    (finiteHistoryScalarRidgeDesign lambda actionFeature)
    (finiteHistoryScalarRidgeRadius actionFeature R delta lambda S)
    (finiteHistoryFixedActionFeature actionFeature)
    (measurable_finiteHistoryScalarRidgeOptimisticScore
      lambda actionFeature R delta S)

/-- Feature selected by the concrete scalar-ridge history selector. -/
noncomputable def finiteHistoryScalarRidgeSelectedFeature
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin K) Real n) :
    Feature -> Real :=
  actionFeature
    (finiteHistoryScalarRidgeOptimisticAction
      hK lambda actionFeature R delta S n history)

/--
On the canonical recursive trajectory, the feature of the actual successor
arm is almost surely the feature selected from the realized scalar-ridge state.
-/
theorem
    canonicalHistoryTrajectory_observedFeature_succ_ae_eq_finiteHistoryScalarRidgeSelectedFeature
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
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment,
      actionFeature
          (Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1)) =
        finiteHistoryScalarRidgeSelectedFeature
          hK lambda actionFeature R delta S n
          (History.finitePairHistoryOfTrace
            (Thompson.canonicalHistoryTrajectoryAction trajectory)
            (Thompson.canonicalHistoryTrajectoryReward trajectory) n) := by
  simpa only [finiteHistoryScalarRidgeOptimisticAlgorithm,
    finiteHistoryScalarRidgeSelectedFeature,
    finiteHistoryScalarRidgeOptimisticAction,
    finiteHistoryFixedActionFeature,
    finiteHistoryOptimisticSelectedFeature] using
    canonicalHistoryTrajectory_candidateFeature_succ_ae_eq_selectedFeature
      hK
      (finiteHistoryScalarRidgeEstimate lambda actionFeature)
      (finiteHistoryScalarRidgeDesign lambda actionFeature)
      (finiteHistoryScalarRidgeRadius actionFeature R delta lambda S)
      (finiteHistoryFixedActionFeature actionFeature)
      (measurable_finiteHistoryScalarRidgeOptimisticScore
        lambda actionFeature R delta S)
      environment n

end OFUL
end BanditRLProof
