import BanditRLProof.OFULExpectedRegretConsistency
import BanditRLProof.OFULScheduledBoundedStoppingTimeExpectedRegretAsymptotics

/-!
# Expected-average consistency for bounded-stopping-time OFUL

This module normalizes the fixed-model horizon-indexed expected stopped
pseudo-regret family by the number of available rounds. The policy at horizon
`T` retains the telescoping schedule with outer budget `1 / (T + 1)`.
-/

namespace BanditRLProof.OFUL

open Filter Real MeasureTheory
open scoped Topology

universe u

/--
The explicit tuned bounded-stopping-time expected pseudo-regret budget is
`o(T + 1)`.
-/
theorem
    telescopingStandardExpectedPseudoRegretBound_isLittleO_natCast_succ
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (R : Real) (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (L2 : Real) (hL2 : 0 <= L2) :
    (fun horizon : Nat =>
      telescopingStandardExpectedPseudoRegretBound
        (Feature := Feature) R lambda S horizon L2) =o[atTop]
      (fun horizon : Nat => (((horizon + 1 : Nat) : Real))) :=
  (telescopingStandardExpectedPseudoRegretBound_isBigO_sqrt_mul_log
    (Feature := Feature) R lambda hlambda S L2 hL2).trans_isLittleO
      sqrt_mul_log_succ_isLittleO_natCast_succ

/--
For fixed model parameters and a horizon-indexed stopping-time family bounded
by its horizon, the named expected stopped pseudo-regret is `o(T + 1)`.
-/
theorem
    canonicalTelescopingStandardExpectedStoppedPseudoRegret_isLittleO_natCast_succ
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (S : Real) (hS : 0 <= S)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment)
    (tau : Nat -> (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : forall maxHorizon,
      IsStoppingTime
        (canonicalHistoryTrajectoryAllRoundFiltration (K := K))
        (tau maxHorizon))
    (htau_le : forall maxHorizon trajectory,
      tau maxHorizon trajectory <= (maxHorizon : WithTop Nat)) :
    (canonicalTelescopingStandardExpectedStoppedPseudoRegret
      hK lambda thetaStar actionFeature R S environment best tau) =o[atTop]
      (fun horizon : Nat => (((horizon + 1 : Nat) : Real))) :=
  (canonicalTelescopingStandardExpectedStoppedPseudoRegret_isBigO_sqrt_mul_log
    hK lambda hlambda thetaStar actionFeature R hR S hS environment
    L2 hL2 hactionFeatureBound hL2lambda best hbest source
    tau htau htau_le).trans_isLittleO
      sqrt_mul_log_succ_isLittleO_natCast_succ

/--
The expected stopped pseudo-regret per available round for the
horizon-indexed telescoping-schedule policy and stopping-time family.
-/
noncomputable def canonicalTelescopingStandardExpectedAverageStoppedPseudoRegret
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (best : Fin K)
    (tau : Nat -> (Nat -> Fin K × Real) -> WithTop Nat)
    (horizon : Nat) : Real :=
  canonicalTelescopingStandardExpectedStoppedPseudoRegret
    hK lambda thetaStar actionFeature R S environment best tau horizon /
      (((horizon + 1 : Nat) : Real))

/--
For fixed model parameters and any horizon-indexed canonical stopping-time
family bounded pointwise by its horizon, expected stopped pseudo-regret per
available round converges to zero.
-/
theorem
    canonicalTelescopingStandardExpectedAverageStoppedPseudoRegret_tendsto_zero
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (S : Real) (hS : 0 <= S)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment)
    (tau : Nat -> (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : forall maxHorizon,
      IsStoppingTime
        (canonicalHistoryTrajectoryAllRoundFiltration (K := K))
        (tau maxHorizon))
    (htau_le : forall maxHorizon trajectory,
      tau maxHorizon trajectory <= (maxHorizon : WithTop Nat)) :
    Tendsto
      (canonicalTelescopingStandardExpectedAverageStoppedPseudoRegret
        hK lambda thetaStar actionFeature R S environment best tau)
      atTop (nhds 0) := by
  have hlimit :=
    (canonicalTelescopingStandardExpectedStoppedPseudoRegret_isLittleO_natCast_succ
      hK lambda hlambda thetaStar actionFeature R hR S hS environment
      L2 hL2 hactionFeatureBound hL2lambda best hbest source
      tau htau htau_le).tendsto_div_nhds_zero
  convert hlimit using 1

end BanditRLProof.OFUL
