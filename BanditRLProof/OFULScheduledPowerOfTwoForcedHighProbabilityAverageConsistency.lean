import BanditRLProof.OFULScheduledPowerOfTwoForcedHighProbabilityAverageRegret

/-!
# Fixed-confidence average consistency for power-of-two forced OFUL

This module squeezes complete pseudo-regret per round to zero on every
trajectory outside the existing all-horizon violation event. It then bounds
the set of trajectories where this limit fails by the same fixed outer
confidence budget, under the same policy and canonical measure.
-/

namespace BanditRLProof.OFUL

open Filter MeasureTheory Set
open scoped ENNReal Topology

universe u

/--
Complete fixed-best average pseudo-regret tends to zero on every trajectory
outside the fixed-model power-of-two forced all-horizon violation event.
-/
theorem
    powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret_tendsto_zero_of_not_mem_allHorizonViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real)
    (delta : Real) (hdelta : 0 < delta)
    (S L2 : Real) (hL2 : 0 <= L2)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (trajectory : Nat -> Fin K × Real)
    (hnot :
      trajectory ∉
        powerOfTwoForcedCanonicalAsymptoticHighProbabilityPseudoRegretAllHorizonViolationSet
          lambda thetaStar actionFeature R delta S L2 best) :
    Tendsto
      (fun horizon =>
        powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret
          thetaStar actionFeature best horizon trajectory)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro horizon
    unfold powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret
    exact div_nonneg
      (by
        simpa [canonicalStandardHighProbabilityPseudoRegret] using
          canonicalHistoryTrajectorySumRangeAllFixedComparatorGap_nonneg
            thetaStar actionFeature horizon best hbest trajectory)
      (by positivity)
  · intro horizon
    exact
      powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret_le_averageBound_of_not_mem_allHorizonViolationSet
        lambda thetaStar actionFeature R delta S L2 best trajectory hnot horizon
  · exact
      powerOfTwoForcedScalarHighProbabilityAveragePseudoRegretBound_tendsto_zero
        (Feature := Feature) R delta hdelta lambda hlambda S L2 hL2

/--
The trajectories where complete fixed-best average pseudo-regret does not
converge to zero.
-/
noncomputable def
    powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegretConsistencyFailureSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K) : Set (Nat -> Fin K × Real) :=
  {trajectory |
    ¬ Tendsto
      (fun horizon =>
        powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret
          thetaStar actionFeature best horizon trajectory)
      atTop (nhds 0)}

/--
Failure of trajectory-level average consistency can only occur inside the
existing all-horizon violation event.
-/
theorem
    powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegretConsistencyFailureSet_subset_allHorizonViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real)
    (delta : Real) (hdelta : 0 < delta)
    (S L2 : Real) (hL2 : 0 <= L2)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best) :
    powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegretConsistencyFailureSet
        thetaStar actionFeature best ⊆
      powerOfTwoForcedCanonicalAsymptoticHighProbabilityPseudoRegretAllHorizonViolationSet
        lambda thetaStar actionFeature R delta S L2 best := by
  intro trajectory hfailure
  change
    ¬ Tendsto
      (fun horizon =>
        powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret
          thetaStar actionFeature best horizon trajectory)
      atTop (nhds 0) at hfailure
  by_contra hnot
  exact hfailure
    (powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret_tendsto_zero_of_not_mem_allHorizonViolationSet
      lambda hlambda thetaStar actionFeature R delta hdelta S L2 hL2 best hbest
      trajectory hnot)

/--
Complete fixed-confidence trajectory-level average-consistency theorem for one
power-of-two forced policy. Outside the unchanged all-horizon event average
pseudo-regret tends to zero, and the set of trajectories where this convergence
fails has outer measure at most `delta` under the same canonical measure.
-/
theorem
    powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret_tendsto_zero_off_violation_and_consistencyFailure_tail_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real) (hS : 0 <= S)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    (forall trajectory,
      trajectory ∉
          powerOfTwoForcedCanonicalAsymptoticHighProbabilityPseudoRegretAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2 best ->
        Tendsto
          (fun horizon =>
            powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret
              thetaStar actionFeature best horizon trajectory)
          atTop (nhds 0)) ∧
      Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment
          (powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegretConsistencyFailureSet
            thetaStar actionFeature best) <=
        ENNReal.ofReal delta := by
  constructor
  · intro trajectory hnot
    exact
      powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret_tendsto_zero_of_not_mem_allHorizonViolationSet
        lambda hlambda thetaStar actionFeature R delta hdelta S L2 hL2 best hbest
        trajectory hnot
  · have hparent :=
      powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegret_averageBudget_tendsto_zero_nonneg_and_allHorizon_tail_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S hS forcedAction environment
        L2 hL2 hactionFeatureBound hL2lambda best hbest source
    exact
      (measure_mono
        (powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegretConsistencyFailureSet_subset_allHorizonViolationSet
          lambda hlambda thetaStar actionFeature R delta hdelta S L2 hL2 best hbest)).trans
        hparent.2.2.2

end BanditRLProof.OFUL
