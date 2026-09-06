import Mathlib.Probability.Independence.InfinitePi
import BanditRLProof.Core

/-!
# Independence foundation wrappers

This module exposes small Mathlib-backed independence imports under the project
namespace.  It stays at the product-coordinate source layer: no bandit policy,
filtration, conditional expectation, or regret theorem is introduced here.
-/

namespace BanditRLProof
namespace IndependenceFoundation

/--
Coordinate transforms under an infinite product measure form an independent
family.

This is the generic `IID-REWARD-FAMILY` import wrapper.  It is a project-local
surface over Mathlib's `ProbabilityTheory.iIndepFun_infinitePi`.
-/
theorem iIndepFun_infinitePi_coord
    {Idx : Type u} {Omega : Idx -> Type v} {Target : Idx -> Type w}
    [mOmega : forall i, MeasurableSpace (Omega i)]
    [mTarget : forall i, MeasurableSpace (Target i)]
    (coordLaw : forall i, MeasureTheory.Measure (Omega i))
    [forall i, MeasureTheory.IsProbabilityMeasure (coordLaw i)]
    (X : forall i, Omega i -> Target i)
    (hX : forall i, Measurable (X i)) :
    ProbabilityTheory.iIndepFun
      (fun i omega => X i (omega i))
      (MeasureTheory.Measure.infinitePi coordLaw) := by
  exact
    ProbabilityTheory.iIndepFun_infinitePi
      (P := coordLaw)
      (X := X)
      (mX := hX)

/--
The coordinate projections of an infinite product reward trace are independent.

This is the reward-trace specialization of `iIndepFun_infinitePi_coord`.
-/
theorem iIndepFun_rewardTrace_infinitePi
    {Reward : Type u} [MeasurableSpace Reward]
    (coordLaw : Nat -> MeasureTheory.Measure Reward)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)] :
    ProbabilityTheory.iIndepFun
      (fun t (omega : RewardTrace Reward) => omega t)
      (MeasureTheory.Measure.infinitePi coordLaw) := by
  simpa [RewardTrace] using
    (iIndepFun_infinitePi_coord
      (coordLaw := coordLaw)
      (X := fun _t r => r)
      (hX := fun _t => measurable_id))

end IndependenceFoundation
end BanditRLProof
