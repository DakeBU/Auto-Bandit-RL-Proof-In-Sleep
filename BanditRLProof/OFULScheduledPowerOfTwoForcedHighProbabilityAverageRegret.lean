import BanditRLProof.OFULScheduledPowerOfTwoForcedHighProbabilityRegretRate
import BanditRLProof.OFULExpectedRegretConsistency

/-!
# Vanishing average budget for power-of-two forced OFUL

This module divides the exact fixed-model scalar all-horizon budget by the
number of available rounds. It preserves the same power-of-two forced policy,
canonical measure, violation event, and fixed outer confidence budget.
-/

namespace BanditRLProof.OFUL

open Filter Real MeasureTheory Set
open scoped ENNReal Topology

universe u

/--
The exact scalar power-of-two forced high-probability budget is `o(T + 1)` for
fixed model parameters and fixed positive outer confidence budget.
-/
theorem
    powerOfTwoForcedScalarHighProbabilityPseudoRegretBound_isLittleO_natCast_succ
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (R : Real)
    (delta : Real) (hdelta : 0 < delta)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (L2 : Real) (hL2 : 0 <= L2) :
    (fun horizon : Nat =>
      powerOfTwoForcedScalarHighProbabilityPseudoRegretBound
        (Feature := Feature) R delta lambda S horizon L2) =o[atTop]
      (fun horizon : Nat => (((horizon + 1 : Nat) : Real))) :=
  (powerOfTwoForcedScalarHighProbabilityPseudoRegretBound_isBigO_sqrt_mul_log
    (Feature := Feature) R delta hdelta lambda hlambda S L2 hL2).trans_isLittleO
      sqrt_mul_log_succ_isLittleO_natCast_succ

/-- The exact scalar high-probability budget per available round. -/
noncomputable def powerOfTwoForcedScalarHighProbabilityAveragePseudoRegretBound
    {Feature : Type u} [Fintype Feature]
    (R delta lambda S : Real) (horizon : Nat) (L2 : Real) : Real :=
  powerOfTwoForcedScalarHighProbabilityPseudoRegretBound
      (Feature := Feature) R delta lambda S horizon L2 /
    (((horizon + 1 : Nat) : Real))

/-- The exact scalar high-probability budget per round converges to zero. -/
theorem
    powerOfTwoForcedScalarHighProbabilityAveragePseudoRegretBound_tendsto_zero
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (R : Real)
    (delta : Real) (hdelta : 0 < delta)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (L2 : Real) (hL2 : 0 <= L2) :
    Tendsto
      (powerOfTwoForcedScalarHighProbabilityAveragePseudoRegretBound
        (Feature := Feature) R delta lambda S · L2)
      atTop (nhds 0) := by
  have hlimit :=
    (powerOfTwoForcedScalarHighProbabilityPseudoRegretBound_isLittleO_natCast_succ
      (Feature := Feature) R delta hdelta lambda hlambda S L2 hL2).tendsto_div_nhds_zero
  convert hlimit using 1

/-- Complete fixed-best pseudo-regret per available round. -/
noncomputable def
    powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (horizon : Nat)
    (trajectory : Nat -> Fin K × Real) : Real :=
  canonicalStandardHighProbabilityPseudoRegret
      thetaStar actionFeature best horizon trajectory /
    (((horizon + 1 : Nat) : Real))

/--
Outside the named all-horizon violation event, complete pseudo-regret per round
is bounded by the exact scalar average budget at every horizon.
-/
theorem
    powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret_le_averageBound_of_not_mem_allHorizonViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (best : Fin K)
    (trajectory : Nat -> Fin K × Real)
    (hnot :
      trajectory ∉
        powerOfTwoForcedCanonicalAsymptoticHighProbabilityPseudoRegretAllHorizonViolationSet
          lambda thetaStar actionFeature R delta S L2 best)
    (horizon : Nat) :
    powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret
        thetaStar actionFeature best horizon trajectory <=
      powerOfTwoForcedScalarHighProbabilityAveragePseudoRegretBound
        (Feature := Feature) R delta lambda S horizon L2 := by
  have hregret :
      canonicalStandardHighProbabilityPseudoRegret
          thetaStar actionFeature best horizon trajectory <=
        powerOfTwoForcedScalarHighProbabilityPseudoRegretBound
          (Feature := Feature) R delta lambda S horizon L2 := by
    by_contra hle
    exact hnot ⟨horizon, lt_of_not_ge hle⟩
  unfold
    powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret
    powerOfTwoForcedScalarHighProbabilityAveragePseudoRegretBound
  exact
    (div_le_div_iff_of_pos_right
      (by positivity : (0 : Real) < (((horizon + 1 : Nat) : Real)))).2 hregret

/--
Complete fixed-model average-envelope theorem for one power-of-two forced
policy: the exact scalar average budget tends to zero, it bounds complete
pseudo-regret per round outside the unchanged all-horizon event, pseudo-regret
is nonnegative, and the event has probability at most `delta`.
-/
theorem
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegret_averageBudget_tendsto_zero_nonneg_and_allHorizon_tail_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
    Tendsto
        (powerOfTwoForcedScalarHighProbabilityAveragePseudoRegretBound
          (Feature := Feature) R delta lambda S · L2)
        atTop (nhds 0) ∧
      (forall trajectory,
        trajectory ∉
            powerOfTwoForcedCanonicalAsymptoticHighProbabilityPseudoRegretAllHorizonViolationSet
              lambda thetaStar actionFeature R delta S L2 best ->
          forall horizon,
            powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret
                thetaStar actionFeature best horizon trajectory <=
              powerOfTwoForcedScalarHighProbabilityAveragePseudoRegretBound
                (Feature := Feature) R delta lambda S horizon L2) ∧
      (forall horizon trajectory,
        0 <= canonicalStandardHighProbabilityPseudoRegret
          thetaStar actionFeature best horizon trajectory) ∧
      Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment
          (powerOfTwoForcedCanonicalAsymptoticHighProbabilityPseudoRegretAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2 best) <=
        ENNReal.ofReal delta := by
  have haverage :=
    powerOfTwoForcedScalarHighProbabilityAveragePseudoRegretBound_tendsto_zero
      (Feature := Feature) R delta hdelta lambda hlambda S L2 hL2
  have hpathwise :
      forall trajectory,
        trajectory ∉
            powerOfTwoForcedCanonicalAsymptoticHighProbabilityPseudoRegretAllHorizonViolationSet
              lambda thetaStar actionFeature R delta S L2 best ->
          forall horizon,
            powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret
                thetaStar actionFeature best horizon trajectory <=
              powerOfTwoForcedScalarHighProbabilityAveragePseudoRegretBound
                (Feature := Feature) R delta lambda S horizon L2 := by
    intro trajectory hnot horizon
    exact
      powerOfTwoForcedCanonicalStandardHighProbabilityAveragePseudoRegret_le_averageBound_of_not_mem_allHorizonViolationSet
        lambda thetaStar actionFeature R delta S L2 best trajectory hnot horizon
  have hparent :=
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegret_asymptoticRate_nonneg_and_allHorizon_tail_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS forcedAction environment
      L2 hL2 hactionFeatureBound hL2lambda best hbest source
  exact ⟨haverage, hpathwise, hparent.2.1, hparent.2.2⟩

end BanditRLProof.OFUL
