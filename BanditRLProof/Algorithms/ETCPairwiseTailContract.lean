import BanditRLProof.Algorithms.ETCArgmaxOracle
import BanditRLProof.Algorithms.ETCEmpiricalMean

/-!
# ETC pairwise empirical-mean tail contract surface

This module introduces the narrow contract surface needed between concrete ETC
empirical means and the already compiled concrete argmax wrong-commit
probability wrapper.  It deliberately packages the abstract pairwise-tail
hypothesis without proving any concentration theorem, adding filtration, or
proving final ETC regret.
-/

namespace BanditRLProof
namespace ETC

/--
Abstract non-best pairwise tail contract for fixed-commit ETC empirical means.

This is the `ETC-PAIRWISE-TAIL-CONTRACT-SURFACE` leaf.  It records exactly the
`hpair_tail` shape needed by the concrete argmax filtered-sum probability
wrapper after instantiating `empMean` with `ETC.empMeanAtExploration`.
-/
structure PairwiseEmpMeanTailContract
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal) : Prop where
  bound :
    forall a : Fin K, (a = model.bestArm -> False) ->
      mu {omega : Omega |
        ETC.empMeanAtExploration spec commitArm (reward omega) a >=
          ETC.empMeanAtExploration spec commitArm
            (reward omega) model.bestArm} <= tail a

/--
The concrete argmax wrong-commit probability wrapper consumes the fixed-commit
ETC empirical-mean pairwise-tail contract directly.

This leaf only connects the contract surface to the compiled probability
consumer.  It does not prove the contract, import Hoeffding/sub-Gaussian tails,
introduce filtration, or prove final ETC regret.
-/
theorem prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    (hcontract :
      ETC.PairwiseEmpMeanTailContract
        mu spec model commitArm reward tail) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
      hK
      mu
      model
      (fun omega : Omega =>
        fun a : Fin K =>
          ETC.empMeanAtExploration spec commitArm (reward omega) a)
      tail
      hcontract.bound

end ETC
end BanditRLProof
