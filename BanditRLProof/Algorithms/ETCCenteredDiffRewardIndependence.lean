import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import BanditRLProof.Algorithms.ETCSumRewardsDiff

/-!
# ETC centered reward-difference independence transfer

This module transfers time-coordinate independence of a stochastic reward trace
through the deterministic centered pairwise reward-difference transform used by
the ETC wrong-commit tail route.
-/

namespace BanditRLProof
namespace ETC

/--
If the reward trace coordinates are independent across time, then the centered
pairwise reward-difference summands are independent across time for every
non-best arm.

This is the `ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS` leaf. It only proves the
deterministic-transform part of the reward-law independence obligation. It
does not prove the reward trace coordinates are independent from a kernel or
environment model, and it does not prove any sub-Gaussian witness.
-/
theorem iIndepFun_centeredPairwiseRewardDiff_of_iIndepFun_reward
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu) :
    forall a : Fin K, (a = model.bestArm -> False) ->
      ProbabilityTheory.iIndepFun
        (fun t omega =>
          ETC.centeredPairwiseRewardDiff spec model commitArm reward a t omega)
        mu := by
  intro a _hne
  let transform : Nat -> Rat -> Real := fun t r =>
    (((if ETC.actionWithCommit spec commitArm t = a then
        r - model.mean a else 0) +
      (if ETC.actionWithCommit spec commitArm t = model.bestArm then
        model.mean model.bestArm - r else 0) : Rat) : Real)
  have hcomp :
      ProbabilityTheory.iIndepFun
        (fun t omega => transform t (reward omega t)) mu :=
    h_reward_indep.comp transform (fun _t => measurable_of_countable _)
  simpa [transform, ETC.centeredPairwiseRewardDiff] using hcomp

end ETC
end BanditRLProof
