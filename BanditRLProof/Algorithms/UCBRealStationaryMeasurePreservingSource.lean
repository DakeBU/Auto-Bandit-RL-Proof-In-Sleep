import BanditRLProof.Algorithms.UCBRealStationaryFiniteArmRewardLaws

/-!
# Measure-preserving external sources for stationary UCB

This module constructs `RealStationaryUCBSequence` by pulling the canonical
arm-stream process through a measure-preserving source map. A product-space
specialization permits arbitrary independent nuisance randomness and closes
the armwise-bounded expected-average consistency route without caller-supplied
split conditional laws.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace UCB

/-!
Mathlib's `condDistrib_map` has the required transport content, but rewriting
its pushforward measure can expose proof-valued finite-measure instances. This
equivalent uniqueness proof transports the conditioning and joint maps first.
-/

/-- Conditional distributions pull back through a measure-preserving map. -/
theorem condDistrib_comp_measurePreserving
    {Alpha : Type u} {Beta : Type v} {Output : Type w}
    {Source : Type x}
    [MeasurableSpace Alpha] [MeasurableSpace Beta]
    [MeasurableSpace Output] [StandardBorelSpace Output] [Nonempty Output]
    [MeasurableSpace Source]
    (mu : Measure Source) [IsFiniteMeasure mu]
    (nu : Measure Alpha) [IsFiniteMeasure nu]
    (source : Source -> Alpha) (hsource : MeasurePreserving source mu nu)
    (X : Alpha -> Beta) (Y : Alpha -> Output)
    (hX : Measurable X) (hY : Measurable Y) :
    condDistrib (Y ∘ source) (X ∘ source) mu =ᵐ[mu.map (X ∘ source)]
      condDistrib Y X nu := by
  apply ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (hX.comp hsource.measurable) (hY.comp hsource.measurable)
  calc
    mu.map (fun omega => ((X ∘ source) omega, (Y ∘ source) omega)) =
        nu.map (fun alpha => (X alpha, Y alpha)) := by
      change mu.map ((fun alpha => (X alpha, Y alpha)) ∘ source) = _
      rw [← Measure.map_map (hX.prod hY) hsource.measurable,
        hsource.map_eq]
    _ = nu.map X ⊗ₘ condDistrib Y X nu := by
      exact (ProbabilityTheory.compProd_map_condDistrib hY.aemeasurable).symm
    _ = mu.map (X ∘ source) ⊗ₘ condDistrib Y X nu := by
      rw [← Measure.map_map hX hsource.measurable, hsource.map_eq]

/-- Canonical UCB action trace composed with an external stream source. -/
noncomputable def measurePreservingArmStreamAction
    {Omega : Type u} {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (source : Omega -> ArmRewardStream K) :
    Omega -> ActionTrace (Fin K) :=
  fun omega => armStreamAction hK (c * (sigma2 : Real)) (source omega)

/-- Canonical selected-reward trace composed with an external stream source. -/
noncomputable def measurePreservingArmStreamReward
    {Omega : Type u} {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (source : Omega -> ArmRewardStream K) :
    Omega -> RewardTrace Real :=
  fun omega => armStreamReward hK (c * (sigma2 : Real)) (source omega)

/--
A measure-preserving source of canonical arm streams produces every field of
the local stationary UCB compatibility bundle on the external sample space.
-/
theorem realStationaryUCBSequence_comp_measurePreserving_armStream
    {Omega : Type u} {K : Nat} [NeZero K] [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (source : Omega -> ArmRewardStream K)
    (hsource : MeasurePreserving source mu (armStreamMeasure nu)) :
    RealStationaryUCBSequence mu hK c sigma2 nu
      (measurePreservingArmStreamAction hK c sigma2 source)
      (measurePreservingArmStreamReward hK c sigma2 source) := by
  refine
    { measurable_action := fun t =>
        (measurable_armStreamAction hK (c * (sigma2 : Real)) t).comp
          hsource.measurable
      measurable_reward := fun t =>
        (measurable_armStreamReward hK (c * (sigma2 : Real)) t).comp
          hsource.measurable
      hasLaw_action_zero := ?_
      hasCondDistrib_feedback_zero := ?_
      hasCondDistrib_action := ?_
      hasCondDistrib_feedback := ?_ }
  · change Measure.map
      ((fun stream : ArmRewardStream K =>
        armStreamAction hK (c * (sigma2 : Real)) stream 0) ∘ source) mu = _
    rw [← Measure.map_map
      (measurable_armStreamAction hK (c * (sigma2 : Real)) 0)
      hsource.measurable]
    rw [hsource.map_eq]
  · simpa [measurePreservingArmStreamAction,
      measurePreservingArmStreamReward, Function.comp_def] using
      (condDistrib_comp_measurePreserving mu (armStreamMeasure nu)
        source hsource
        (fun stream : ArmRewardStream K =>
          armStreamAction hK (c * (sigma2 : Real)) stream 0)
        (fun stream : ArmRewardStream K =>
          armStreamReward hK (c * (sigma2 : Real)) stream 0)
        (measurable_armStreamAction hK (c * (sigma2 : Real)) 0)
        (measurable_armStreamReward hK (c * (sigma2 : Real)) 0))
  · intro i
    simpa [measurePreservingArmStreamAction,
      measurePreservingArmStreamReward, Function.comp_def] using
      (condDistrib_comp_measurePreserving mu (armStreamMeasure nu)
        source hsource
        (fun stream : ArmRewardStream K =>
          History.finitePairHistoryOfTrace
            (armStreamAction hK (c * (sigma2 : Real)) stream)
            (armStreamReward hK (c * (sigma2 : Real)) stream) i)
        (fun stream : ArmRewardStream K =>
          armStreamAction hK (c * (sigma2 : Real)) stream (i + 1))
        (History.measurable_finitePairHistoryOfTrace
          (armStreamAction hK (c * (sigma2 : Real)))
          (armStreamReward hK (c * (sigma2 : Real)))
          (measurable_armStreamAction hK (c * (sigma2 : Real)))
          (measurable_armStreamReward hK (c * (sigma2 : Real))) i)
        (measurable_armStreamAction hK (c * (sigma2 : Real)) (i + 1)))
  · intro i
    simpa [measurePreservingArmStreamAction,
      measurePreservingArmStreamReward, Function.comp_def] using
      (condDistrib_comp_measurePreserving mu (armStreamMeasure nu)
        source hsource
        (fun stream : ArmRewardStream K =>
          (History.finitePairHistoryOfTrace
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (armStreamReward hK (c * (sigma2 : Real)) stream) i,
            armStreamAction hK (c * (sigma2 : Real)) stream (i + 1)))
        (fun stream : ArmRewardStream K =>
          armStreamReward hK (c * (sigma2 : Real)) stream (i + 1))
        ((History.measurable_finitePairHistoryOfTrace
            (armStreamAction hK (c * (sigma2 : Real)))
            (armStreamReward hK (c * (sigma2 : Real)))
            (measurable_armStreamAction hK (c * (sigma2 : Real)))
            (measurable_armStreamReward hK (c * (sigma2 : Real))) i).prod
          (measurable_armStreamAction hK (c * (sigma2 : Real)) (i + 1)))
        (measurable_armStreamReward hK (c * (sigma2 : Real)) (i + 1)))

/-- Canonical UCB action on a stream product with auxiliary noise. -/
noncomputable def productNoiseArmStreamAction
    {K : Nat} [NeZero K] {Aux : Type u}
    (hK : 0 < K) (c : Real) (sigma2 : NNReal) :
    ArmRewardStream K × Aux -> ActionTrace (Fin K) :=
  measurePreservingArmStreamAction hK c sigma2 Prod.fst

/-- Canonical selected reward on a stream product with auxiliary noise. -/
noncomputable def productNoiseArmStreamReward
    {K : Nat} [NeZero K] {Aux : Type u}
    (hK : 0 < K) (c : Real) (sigma2 : NNReal) :
    ArmRewardStream K × Aux -> RewardTrace Real :=
  measurePreservingArmStreamReward hK c sigma2 Prod.fst

/-- Product-first projection is a concrete external stationary UCB source. -/
theorem realStationaryUCBSequence_productNoise_armStream
    {K : Nat} [NeZero K] {Aux : Type u} [MeasurableSpace Aux]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (auxMu : Measure Aux) [IsProbabilityMeasure auxMu] :
    RealStationaryUCBSequence ((armStreamMeasure nu).prod auxMu)
      hK c sigma2 nu
      (productNoiseArmStreamAction hK c sigma2)
      (productNoiseArmStreamReward hK c sigma2) := by
  exact realStationaryUCBSequence_comp_measurePreserving_armStream
    ((armStreamMeasure nu).prod auxMu) hK c sigma2 nu
    Prod.fst measurePreserving_fst

/-- Product law for finite Real arm streams and independent auxiliary noise. -/
noncomputable def finiteArmProductNoiseMeasure
    {K : Nat} {Aux : Type u} [MeasurableSpace Aux]
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (auxMu : Measure Aux) : Measure (ArmRewardStream K × Aux) :=
  let nu := finiteArmRealRewardKernel armLaw
  letI : IsMarkovKernel nu :=
    finiteArmRealRewardKernel_isMarkov armLaw hprob
  (armStreamMeasure nu).prod auxMu

/--
Armwise-bounded laws give the canonical logarithmic expected-regret envelope
on a product sample space carrying arbitrary independent auxiliary noise.
-/
theorem productNoiseArmwiseBoundedFiniteArmExpectedRegret_nonneg_and_le
    {K : Nat} [NeZero K] {Aux : Type u} [MeasurableSpace Aux]
    (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (auxMu : Measure Aux) [IsProbabilityMeasure auxMu]
    (hbound : forall arm,
      Filter.Eventually
        (fun x : Real => Set.Icc (lo arm) (hi arm) x) (ae (armLaw arm)))
    (n : Nat) :
    let sigma2 := Concentration.finiteArmPositiveVarianceProxy
      (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
    0 <= realStationaryArmwiseBoundedFiniteArmExpectedRegret
        (finiteArmProductNoiseMeasure armLaw hprob auxMu) armLaw
        (productNoiseArmStreamAction hK 4 sigma2) n /\
      realStationaryArmwiseBoundedFiniteArmExpectedRegret
          (finiteArmProductNoiseMeasure armLaw hprob auxMu) armLaw
          (productNoiseArmStreamAction hK 4 sigma2) n <=
        realStationaryArmwiseBoundedFiniteArmModelCoefficient
            armLaw hprob lo hi *
          (1 + Real.log ((n + 1 : Nat) : Real)) := by
  dsimp only
  let nu := finiteArmRealRewardKernel armLaw
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy
    (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
  letI : IsMarkovKernel nu :=
    finiteArmRealRewardKernel_isMarkov armLaw hprob
  change
    0 <= realStationaryArmwiseBoundedFiniteArmExpectedRegret
        ((armStreamMeasure nu).prod auxMu) armLaw
        (productNoiseArmStreamAction hK 4 sigma2) n /\
      realStationaryArmwiseBoundedFiniteArmExpectedRegret
          ((armStreamMeasure nu).prod auxMu) armLaw
          (productNoiseArmStreamAction hK 4 sigma2) n <=
        realStationaryArmwiseBoundedFiniteArmModelCoefficient
            armLaw hprob lo hi *
          (1 + Real.log ((n + 1 : Nat) : Real))
  exact realStationaryArmwiseBoundedFiniteArmExpectedRegret_nonneg_and_le
    ((armStreamMeasure nu).prod auxMu) hK armLaw hprob lo hi
    (productNoiseArmStreamAction hK 4 sigma2)
    (productNoiseArmStreamReward hK 4 sigma2) hbound
    (realStationaryUCBSequence_productNoise_armStream
      hK 4 sigma2 nu auxMu) n

/--
The expected regret per round of product-noise stationary UCB with armwise
bounded finite Real reward laws tends to zero.
-/
theorem productNoiseArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero
    {K : Nat} [NeZero K] {Aux : Type u} [MeasurableSpace Aux]
    (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (auxMu : Measure Aux) [IsProbabilityMeasure auxMu]
    (hbound : forall arm,
      Filter.Eventually
        (fun x : Real => Set.Icc (lo arm) (hi arm) x) (ae (armLaw arm))) :
    let sigma2 := Concentration.finiteArmPositiveVarianceProxy
      (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
    Tendsto
      (realStationaryArmwiseBoundedFiniteArmExpectedAverageRegret
        (finiteArmProductNoiseMeasure armLaw hprob auxMu) armLaw
        (productNoiseArmStreamAction hK 4 sigma2))
      atTop (nhds 0) := by
  dsimp only
  let nu := finiteArmRealRewardKernel armLaw
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy
    (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
  letI : IsMarkovKernel nu :=
    finiteArmRealRewardKernel_isMarkov armLaw hprob
  change Tendsto
    (realStationaryArmwiseBoundedFiniteArmExpectedAverageRegret
      ((armStreamMeasure nu).prod auxMu) armLaw
      (productNoiseArmStreamAction hK 4 sigma2)) atTop (nhds 0)
  exact
    realStationaryArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero
      ((armStreamMeasure nu).prod auxMu) hK armLaw hprob lo hi
      (productNoiseArmStreamAction hK 4 sigma2)
      (productNoiseArmStreamReward hK 4 sigma2) hbound
      (realStationaryUCBSequence_productNoise_armStream
        hK 4 sigma2 nu auxMu)

end UCB
end BanditRLProof
