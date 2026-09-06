import BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian
import BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses
import BanditRLProof.MartingaleDifference

/-!
# ETC bounded reward source contract

This module packages the stochastic source facts consumed by the bounded-reward
ETC wrong-commit route.  It does not construct those facts from a concrete
environment, product space, kernel, or filtration.
-/

namespace BanditRLProof
namespace ETC

/--
Source contract for the bounded-reward ETC wrong-commit route.

This is intentionally a thin structure: it records trace-level reward-coordinate
independence, a.e. coordinate measurability, a.s. interval bounds, and exact
mean identities over the ETC exploration horizon.
-/
structure BoundedRewardTraceSource
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real) where
  indep :
    ProbabilityTheory.iIndepFun
      (fun t omega => reward omega t) mu
  meas :
    forall t, t < spec.explorationPulls * K ->
      AEMeasurable (fun omega : Omega => (((reward omega t : Rat) : Real))) mu
  bound :
    forall t, t < spec.explorationPulls * K ->
      Filter.Eventually
        (fun omega : Omega =>
          Set.Icc
            (lo (ETC.actionWithCommit spec commitArm t) t)
            (hi (ETC.actionWithCommit spec commitArm t) t)
            (((reward omega t : Rat) : Real)))
        (MeasureTheory.ae mu)
  mean :
    forall t, t < spec.explorationPulls * K ->
      MeasureTheory.integral mu
        (fun omega : Omega => (((reward omega t : Rat) : Real))) =
      (((model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))

/--
A bounded reward source supplies raw reward integrability for the action
actually pulled at time `t`.

This packages the `meas` and `bound` fields into the bounded-to-integrable side
condition consumed by the conditional mean-zero route.
-/
theorem centeredReward_integrable_of_boundedRewardTraceSource
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (t : Nat) (ht : t < spec.explorationPulls * K) :
    MeasureTheory.Integrable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu := by
  exact
    ETC.centeredReward_integrable_of_mem_Icc
      mu reward lo hi (ETC.actionWithCommit spec commitArm t) t
      (source.meas t ht)
      (source.bound t ht)

/--
A bounded reward source supplies the action-matched zero-integral fact for the
centered reward coordinate.

This packages the `meas`, `bound`, and `mean` fields into the zero-integral
side condition consumed by the conditional mean-zero route.
-/
theorem centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (t : Nat) (ht : t < spec.explorationPulls * K) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (((reward omega t -
          model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))) =
      0 := by
  exact
    ETC.centeredReward_integral_eq_zero_of_integral_eq_mean
      mu model reward (ETC.actionWithCommit spec commitArm t) t
      (ETC.centeredReward_integrable_of_boundedRewardTraceSource
        mu spec model commitArm reward lo hi source t ht)
      (source.mean t ht)

/--
The action-matched centered reward at time `t` is measurable with respect to
the shifted generated history filtration at time `t`.

This is the adaptedness side of the fixed-commit martingale-difference route.
-/
theorem measurable_centeredReward_actionWithCommit_historyFiltrationSucc
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (t : Nat) :
    @Measurable Omega Real
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward t)
      inferInstance
      (fun omega : Omega =>
        (((reward omega t -
          model.mean (ETC.actionWithCommit spec commitArm t) :
            Rat) : Real))) := by
  have hreward_t :
      @Measurable Omega Rat
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward t)
        inferInstance
        (fun omega : Omega => reward omega t) := by
    exact
      History.measurable_reward_mem_historyFiltration_of_lt
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward
        (Nat.lt_succ_self t)
  let transform : Rat -> Real := fun r =>
    (((r - model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))
  have htransform : Measurable transform := by
    exact measurable_of_countable transform
  simpa [transform] using htransform.comp hreward_t

/--
The fixed-commit action-matched centered reward process is strongly adapted to
the shifted generated history filtration.
-/
theorem stronglyAdapted_centeredReward_actionWithCommit_historyFiltrationSucc
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t)) :
    MeasureTheory.StronglyAdapted
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward)
      (fun t omega =>
        (((reward omega t -
          model.mean (ETC.actionWithCommit spec commitArm t) :
            Rat) : Real))) := by
  intro t
  exact
    (ETC.measurable_centeredReward_actionWithCommit_historyFiltrationSucc
      spec model commitArm reward hreward t).stronglyMeasurable

/--
A bounded reward source supplies integrability of the action-matched centered
reward coordinate.
-/
theorem centeredReward_actionWithCommit_integrable_of_boundedRewardTraceSource
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (t : Nat) (ht : t < spec.explorationPulls * K) :
    MeasureTheory.Integrable
      (fun omega : Omega =>
        (((reward omega t -
          model.mean (ETC.actionWithCommit spec commitArm t) :
            Rat) : Real))) mu := by
  have hraw :
      MeasureTheory.Integrable
        (fun omega : Omega => (((reward omega t : Rat) : Real))) mu :=
    ETC.centeredReward_integrable_of_boundedRewardTraceSource
      mu spec model commitArm reward lo hi source t ht
  have hconst :
      MeasureTheory.Integrable
        (fun _omega : Omega =>
          (((model.mean (ETC.actionWithCommit spec commitArm t) :
            Rat) : Real))) mu :=
    MeasureTheory.integrable_const _
  have hfun :
      (fun omega : Omega =>
        (((reward omega t -
          model.mean (ETC.actionWithCommit spec commitArm t) :
            Rat) : Real))) =
      (fun omega : Omega =>
        (((reward omega t : Rat) : Real) -
          (((model.mean (ETC.actionWithCommit spec commitArm t) :
            Rat) : Real)))) := by
    funext omega
    simp [Rat.cast_sub]
  rw [hfun]
  exact hraw.sub hconst

/--
A bounded reward source supplies the succ-indexed conditional mean-zero witness
for the fixed-commit shifted history filtration.

The source gives reward-coordinate independence and the action-matched
zero-integral identity.  The action equality rewrites that identity into the
sampled-arm shape consumed by the reward-level conditional mean-zero wrapper.
-/
theorem centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (b : Fin K) (i : Nat)
    (hact : ETC.actionWithCommit spec commitArm (i + 1) = b)
    (ht : i + 1 < spec.explorationPulls * K) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (MeasureTheory.condExp
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward i)
        mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  have h_integral_action :
      MeasureTheory.integral mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            model.mean (ETC.actionWithCommit spec commitArm (i + 1)) :
              Rat) : Real))) = 0 :=
    ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean
      mu spec model commitArm reward lo hi source (i + 1) ht
  have h_integral :
      MeasureTheory.integral mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))) = 0 := by
    simpa [hact] using h_integral_action
  exact
    ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_iIndepFun_reward
      (mOmega := mOmega)
      mu spec model commitArm reward hreward source.indep b i h_integral

/--
Bounded fixed-commit rewards form a finite-prefix martingale-difference
witness after centering by the action-matched arm mean.

This packages the adaptedness, integrability, and succ-indexed conditional
mean-zero fields.  It remains a witness surface, not a final martingale
stopping or regret theorem.
-/
theorem centeredReward_actionWithCommit_succMartingaleDifferencePrefix_of_boundedRewardTraceSource
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (n : Nat) (hn : n <= spec.explorationPulls * K) :
    MartingaleDiff.SuccMartingaleDifferencePrefix
      mu
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward)
      (fun t omega =>
        (((reward omega t -
          model.mean (ETC.actionWithCommit spec commitArm t) :
            Rat) : Real)))
      n := by
  refine
    { stronglyAdapted :=
        ETC.stronglyAdapted_centeredReward_actionWithCommit_historyFiltrationSucc
          spec model commitArm reward hreward
      integrable := ?_
      condExp_succ_eq_zero := ?_ }
  · intro t ht
    exact
      ETC.centeredReward_actionWithCommit_integrable_of_boundedRewardTraceSource
        mu spec model commitArm reward lo hi source t (lt_of_lt_of_le ht hn)
  · intro i hsucc
    exact
      ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource
        (mOmega := mOmega)
        mu spec model commitArm reward lo hi source hreward
        (ETC.actionWithCommit spec commitArm (i + 1)) i rfl
        (lt_of_lt_of_le hsucc hn)

/--
A bounded reward source contract yields the per-coordinate centered reward
sub-Gaussian witness used by the reward-law route.
-/
theorem centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (t : Nat)
    (ht : t < spec.explorationPulls * K) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun omega : Omega =>
        (((reward omega t -
          model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real)))
      (ETC.centeredRewardBoundVarianceProxy
        lo hi (ETC.actionWithCommit spec commitArm t) t) mu := by
  exact
    ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean
      mu model reward lo hi (ETC.actionWithCommit spec commitArm t) t
      (source.meas t ht)
      (source.bound t ht)
      (source.mean t ht)

/--
A bounded reward source supplies the succ-indexed conditional MGF witness for
the fixed-commit shifted history filtration.

The source only records action-matched boundedness and exact means, so this
wrapper keeps the concrete reward measurability contract explicit.  The action
equality rewrites the action-matched unconditional sub-Gaussian witness into the
sampled-arm shape consumed by the reward-level conditional witness package.
-/
theorem centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_boundedRewardTraceSource
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (b : Fin K) (i : Nat)
    (hact : ETC.actionWithCommit spec commitArm (i + 1) = b)
    (ht : i + 1 < spec.explorationPulls * K) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward i)
      ((History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) - model.mean b : Rat) : Real)))
      (ETC.centeredRewardBoundVarianceProxy lo hi b (i + 1)) mu := by
  have h_subG_action :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            model.mean (ETC.actionWithCommit spec commitArm (i + 1)) :
              Rat) : Real)))
        (ETC.centeredRewardBoundVarianceProxy lo hi
          (ETC.actionWithCommit spec commitArm (i + 1)) (i + 1)) mu :=
    ETC.centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource
      mu spec model commitArm reward lo hi source (i + 1) ht
  have h_subG :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real)))
        (ETC.centeredRewardBoundVarianceProxy lo hi b (i + 1)) mu := by
    simpa [hact] using h_subG_action
  exact
    ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward
      (mOmega := mOmega)
      mu spec model commitArm reward hreward source.indep b i
      (ETC.centeredRewardBoundVarianceProxy lo hi b (i + 1)) h_subG

/--
Construct the reward-level conditional sub-Gaussian witness package from a
bounded reward source.

This is the bounded/source assembly leaf: bounded exact-mean rewards provide
the zeroth unconditional MGF and the later conditional MGF witnesses via the
independence bridge, while tail domination remains an explicit contract for the
consumer theorem.
-/
noncomputable def centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (tail : Fin K -> ENNReal)
    (horizon_pos : 0 < spec.explorationPulls * K)
    (htail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ENNReal.ofReal
          (Real.exp
            (-(ETC.centeredPairwiseGapThreshold spec model a) ^ 2 /
              (2 *
                (((Finset.range (spec.explorationPulls * K)).sum
                  (fun t =>
                    ETC.centeredPairwiseRewardDiffVarianceProxy
                      spec model commitArm
                      (ETC.centeredRewardBoundVarianceProxy lo hi) a t) :
                    NNReal) : Real)))) <=
          tail a) :
    ETC.CenteredRewardCondSubGaussianWitnesses
      mu spec model commitArm reward tail where
  cReward := ETC.centeredRewardBoundVarianceProxy lo hi
  hreward := hreward
  subG0 := by
    intro b hb
    have h_subG_action :
        ProbabilityTheory.HasSubgaussianMGF
          (fun omega : Omega =>
            (((reward omega 0 -
              model.mean (ETC.actionWithCommit spec commitArm 0) :
                Rat) : Real)))
          (ETC.centeredRewardBoundVarianceProxy lo hi
            (ETC.actionWithCommit spec commitArm 0) 0) mu :=
      ETC.centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource
        mu spec model commitArm reward lo hi source 0 horizon_pos
    simpa [hb] using h_subG_action
  condSubG := by
    intro i hi_idx b hb
    have ht : i + 1 < spec.explorationPulls * K := by
      omega
    exact
      ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_boundedRewardTraceSource
        (mOmega := mOmega)
        mu spec model commitArm reward lo hi source hreward b i hb ht
  tail_bound := htail

/--
Consume a bounded reward source contract through the conditional
sub-Gaussian route to obtain the fixed-commit pairwise empirical-mean tail
contract.

This theorem closes the local source-to-tail-contract chain for fixed
`actionWithCommit`; it still keeps the final tail domination contract explicit
and does not address arbitrary policy predictability.
-/
theorem pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (tail : Fin K -> ENNReal)
    (horizon_pos : 0 < spec.explorationPulls * K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (htail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ENNReal.ofReal
          (Real.exp
            (-(ETC.centeredPairwiseGapThreshold spec model a) ^ 2 /
              (2 *
                (((Finset.range (spec.explorationPulls * K)).sum
                  (fun t =>
                    ETC.centeredPairwiseRewardDiffVarianceProxy
                      spec model commitArm
                      (ETC.centeredRewardBoundVarianceProxy lo hi) a t) :
                    NNReal) : Real)))) <=
          tail a) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail := by
  exact
    ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses
      mu spec model commitArm reward tail hexplorationPulls_pos
      (ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses
        mu spec model commitArm reward tail
        (ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource
          (mOmega := mOmega)
          mu spec model commitArm reward lo hi source hreward tail
          horizon_pos htail))

/--
Consume a bounded reward source contract through the conditional
sub-Gaussian route to obtain the fixed-commit argmax-oracle wrong-commit
probability wrapper.

This is the probability-facing wrapper for the bounded/source conditional route;
the numerical tail budget is still supplied explicitly by `htail`.
-/
theorem prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_boundedRewardTraceSource_condSubGaussian
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (tail : Fin K -> ENNReal)
    (horizon_pos : 0 < spec.explorationPulls * K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (htail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ENNReal.ofReal
          (Real.exp
            (-(ETC.centeredPairwiseGapThreshold spec model a) ^ 2 /
              (2 *
                (((Finset.range (spec.explorationPulls * K)).sum
                  (fun t =>
                    ETC.centeredPairwiseRewardDiffVarianceProxy
                      spec model commitArm
                      (ETC.centeredRewardBoundVarianceProxy lo hi) a t) :
                    NNReal) : Real)))) <=
          tail a) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract
      hK mu spec model commitArm reward tail
      (ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian
        (mOmega := mOmega)
        mu spec model commitArm reward lo hi source hreward tail
        horizon_pos hexplorationPulls_pos htail)

/--
Construct the reward-level conditional witness package from a bounded reward
source when the caller chooses the canonical centered-diff exponential tail.

This removes the explicit tail-domination assumption from
`centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource` for the
fixed `actionWithCommit` route.
-/
noncomputable def centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource_canonicalTail
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (horizon_pos : 0 < spec.explorationPulls * K) :
    ETC.CenteredRewardCondSubGaussianWitnesses
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource
      (mOmega := mOmega)
      mu spec model commitArm reward lo hi source hreward
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))
      horizon_pos
      (by
        intro a _hne
        simp [ETC.centeredDiffSubGaussianTail])

/--
Produce the fixed-commit pairwise empirical-mean tail contract from a bounded
reward source through the conditional sub-Gaussian route, using the canonical
centered-diff exponential tail.
-/
theorem pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian_canonicalTail
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (horizon_pos : 0 < spec.explorationPulls * K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))
      hexplorationPulls_pos
      (ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses
        mu spec model commitArm reward
        (ETC.centeredDiffSubGaussianTail spec model
          (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
            (ETC.centeredRewardBoundVarianceProxy lo hi)))
        (ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource_canonicalTail
          (mOmega := mOmega)
          mu spec model commitArm reward lo hi source hreward horizon_pos))

/--
Probability-facing fixed-commit bounded-source conditional sub-Gaussian route
with the canonical centered-diff exponential tail budget.

This theorem removes the explicit `htail` contract from
`prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_boundedRewardTraceSource_condSubGaussian`.
-/
theorem prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource_condSubGaussian
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (horizon_pos : 0 < spec.explorationPulls * K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract
      hK mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))
      (ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian_canonicalTail
        (mOmega := mOmega)
        mu spec model commitArm reward lo hi source hreward
        horizon_pos hexplorationPulls_pos)

/--
Consume a bounded reward source contract to obtain the concrete argmax-oracle
wrong-commit probability bound.
-/
theorem prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_bounded_centered
      hK mu spec model commitArm reward lo hi hexplorationPulls_pos
      source.indep source.meas source.bound source.mean

end ETC
end BanditRLProof
