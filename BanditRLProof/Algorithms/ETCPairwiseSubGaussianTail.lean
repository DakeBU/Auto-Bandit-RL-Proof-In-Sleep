import BanditRLProof.Algorithms.ETCPairwiseTailContract
import BanditRLProof.ConcentrationSubGaussian

/-!
# ETC pairwise sub-Gaussian tail producer surface

This module connects the reusable independent sub-Gaussian finite-sum tail
wrapper to the fixed-commit ETC pairwise empirical-mean tail contract.  It
does not instantiate a reward law, prove independence for ETC rewards, add
filtration, or prove final ETC regret.
-/

namespace BanditRLProof
namespace ETC

/--
Build the fixed-commit ETC pairwise empirical-mean tail contract from abstract
independent sub-Gaussian sum witnesses for every non-best arm.

This is the `ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS` bridge.  The event inclusion
field is intentionally explicit: later leaves must prove that the ETC
empirical-mean comparison event is contained in the corresponding centered
reward-difference sum event.
-/
theorem pairwiseEmpMeanTailContract_of_subGaussian_event_bounds
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    {Idx : Type v}
    (idx : Finset Idx)
    (X : Fin K -> Idx -> Omega -> Real)
    (c : Fin K -> Idx -> NNReal)
    (eps : Fin K -> Real)
    (h_indep :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ProbabilityTheory.iIndepFun (X a) mu)
    (h_subG :
      forall a : Fin K, (a = model.bestArm -> False) ->
        forall i, i ∈ idx ->
          ProbabilityTheory.HasSubgaussianMGF ((X a) i) ((c a) i) mu)
    (heps :
      forall a : Fin K, (a = model.bestArm -> False) ->
        0 <= eps a)
    (hsubset :
      forall a : Fin K, (a = model.bestArm -> False) ->
        Set.Subset
          {omega : Omega |
            ETC.empMeanAtExploration spec commitArm (reward omega) a >=
              ETC.empMeanAtExploration spec commitArm
                (reward omega) model.bestArm}
          {omega : Omega | eps a <= idx.sum (fun i => X a i omega)})
    (htail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ENNReal.ofReal
          (Real.exp
            (-(eps a) ^ 2 /
              (2 * ((idx.sum (c a) : NNReal) : Real)))) <= tail a) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail := by
  refine ⟨?_⟩
  intro a hne
  exact
    (mu.mono (hsubset a hne)).trans
      ((Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun
        (mu := mu)
        (X := X a)
        (c := c a)
        (s := idx)
        (h_indep a hne)
        (h_subG a hne)
        (heps a hne)).trans
        (htail a hne))

end ETC
end BanditRLProof
