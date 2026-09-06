import BanditRLProof.OFULExpectedRegretAsymptotics

/-!
# Expected-average consistency for canonical OFUL

This module turns the fixed-model asymptotic expected pseudo-regret bound into
convergence of expected pseudo-regret per played round. The generated
algorithm still uses the horizon-dependent parameter `1 / (T + 1)^2`.
-/

namespace BanditRLProof.OFUL

open Filter Real
open scoped Topology

universe u

theorem sqrt_mul_log_succ_isLittleO_natCast_succ :
    (fun horizon : Nat =>
      Real.sqrt (((horizon + 1 : Nat) : Real)) *
        Real.log (((horizon + 1 : Nat) : Real))) =o[atTop]
    (fun horizon : Nat => (((horizon + 1 : Nat) : Real))) := by
  let n : Nat -> Real := fun horizon => (((horizon + 1 : Nat) : Real))
  have hn_tendsto : Tendsto n atTop atTop := by
    exact (tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop
  have hlog :
      (fun horizon => Real.log (n horizon)) =o[atTop]
        (fun horizon => Real.sqrt (n horizon)) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop
        (show 0 < (1 / (2 : Real)) by norm_num)).comp_tendsto hn_tendsto
  have hprod :=
    hlog.mul_isBigO
      (Asymptotics.isBigO_refl (fun horizon => Real.sqrt (n horizon)) atTop)
  refine hprod.congr (fun horizon => by ring) (fun horizon => ?_)
  rw [Real.mul_self_sqrt]
  dsimp [n]
  positivity

theorem standardExpectedPseudoRegretBound_isLittleO_natCast_succ
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (R : Real) (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (L2 : Real) (hL2 : 0 <= L2) :
    (fun horizon : Nat =>
      standardExpectedPseudoRegretBound
        (Feature := Feature) R lambda S horizon L2) =o[atTop]
    (fun horizon : Nat => (((horizon + 1 : Nat) : Real))) :=
  (standardExpectedPseudoRegretBound_isBigO_sqrt_mul_log
    (Feature := Feature) R lambda hlambda S L2 hL2).trans_isLittleO
      sqrt_mul_log_succ_isLittleO_natCast_succ

theorem canonicalStandardExpectedPseudoRegret_isLittleO_natCast_succ
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
      hK thetaStar actionFeature R S environment) :
    (canonicalStandardExpectedPseudoRegret
      hK lambda thetaStar actionFeature R S environment best) =o[atTop]
    (fun horizon : Nat => (((horizon + 1 : Nat) : Real))) :=
  (canonicalStandardExpectedPseudoRegret_isBigO_sqrt_mul_log
    hK lambda hlambda thetaStar actionFeature R hR S hS environment
    L2 hL2 hactionFeatureBound hL2lambda best hbest source).trans_isLittleO
      sqrt_mul_log_succ_isLittleO_natCast_succ

noncomputable def canonicalStandardExpectedAveragePseudoRegret
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (best : Fin K)
    (horizon : Nat) : Real :=
  canonicalStandardExpectedPseudoRegret
    hK lambda thetaStar actionFeature R S environment best horizon /
      (((horizon + 1 : Nat) : Real))

theorem canonicalStandardExpectedAveragePseudoRegret_tendsto_zero
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
      hK thetaStar actionFeature R S environment) :
    Tendsto
      (canonicalStandardExpectedAveragePseudoRegret
        hK lambda thetaStar actionFeature R S environment best)
      atTop (nhds 0) := by
  have hlimit :=
    (canonicalStandardExpectedPseudoRegret_isLittleO_natCast_succ
      hK lambda hlambda thetaStar actionFeature R hR S hS environment
      L2 hL2 hactionFeatureBound hL2lambda best hbest source).tendsto_div_nhds_zero
  convert hlimit using 1

end BanditRLProof.OFUL
