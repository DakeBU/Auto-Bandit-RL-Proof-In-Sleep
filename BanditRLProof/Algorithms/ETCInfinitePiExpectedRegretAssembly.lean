import BanditRLProof.Algorithms.ETCExpectedRegretAssembly
import BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource
import BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# ETC expected-regret assembly from an infinite product source

This module instantiates the abstract lower-integral wrong-commit regret
assembly with the concrete finite-argmax oracle and the infinite-product
bounded-reward wrong-commit probability bound.  The Real/Bochner wrapper still
remains fixed-product and fixed-exploration, not the final adaptive ETC
theorem.
-/

namespace BanditRLProof
namespace ETC

/--
The finite argmax commit arm selected from the fixed-commit exploration sample.

This is only a naming wrapper around the existing argmax commit oracle and
`ETC.empMeanAtExploration`; it does not add a new probability or filtration
assumption.
-/
noncomputable def fixedProductArgmaxCommit
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (omega : RewardTrace Rat) : Fin K :=
  (ETC.argmaxCommitOracle model.hK).choose
    (fun a : Fin K =>
      ETC.empMeanAtExploration spec baseCommitArm omega a)

/--
The ETC action trace that explores with `baseCommitArm` and then commits to the
finite argmax empirical-mean arm selected from that exploration sample.
-/
noncomputable def fixedProductArgmaxAction
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (omega : RewardTrace Rat) : ActionTrace (Fin K) :=
  ETC.actionWithCommit spec
    (ETC.fixedProductArgmaxCommit spec model baseCommitArm omega)

/--
Named RHS budget for the fixed product-coordinate max-gap lower-integral ETC
regret wrapper.

This is still an `ENNReal.ofReal` surrogate budget.  It does not claim Bochner
or Rat-valued expected regret.
-/
noncomputable def fixedProductMaxGapLintegralRegretBound
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real) : ENNReal :=
  ENNReal.ofReal
    (((((Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => model.gap a)) *
      (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
  ENNReal.ofReal
    ((((((r : Nat) : Rat) * model.maxGap : Rat) : Real))) *
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model baseCommitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))

/--
Named ENNReal wrong-commit tail budget used by the fixed product-coordinate
ETC argmax route.
-/
noncomputable def fixedProductWrongCommitTailBudget
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (lo hi : Fin K -> Nat -> Real) : ENNReal :=
  ((Finset.univ : Finset (Fin K)).filter
    (fun a : Fin K => a = model.bestArm -> False)).sum
    (ETC.centeredDiffSubGaussianTail spec model
      (ETC.centeredPairwiseRewardDiffVarianceProxy spec model baseCommitArm
        (ETC.centeredRewardBoundVarianceProxy lo hi)))

/--
Real-valued view of the fixed product-coordinate wrong-commit tail budget.
-/
noncomputable def fixedProductWrongCommitTailBudgetReal
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (lo hi : Fin K -> Nat -> Real) : Real :=
  (ETC.fixedProductWrongCommitTailBudget spec model baseCommitArm lo hi).toReal

/--
Named Real RHS for the fixed product-coordinate bad-gap Bochner ETC regret
assembly.
-/
noncomputable def fixedProductBadGapIntegralRegretBoundReal
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (badGapBound : Rat)
    (lo hi : Fin K -> Nat -> Real) : Real :=
  let base : Real :=
    (((((Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => model.gap a)) *
      (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real))
  let suffix : Real :=
    (((((r : Nat) : Rat) * badGapBound : Rat) : Real))
  base + suffix *
    ETC.fixedProductWrongCommitTailBudgetReal
      spec model baseCommitArm lo hi

/--
Named Real RHS for the conservative fixed product-coordinate sum-gap Bochner
ETC regret wrapper.

This is the sum-gap specialization of
`fixedProductBadGapIntegralRegretBoundReal`; it removes the explicit
`badGapBound` parameter by using the total finite sum of model gaps as a
conservative non-best suffix gap bound.
-/
noncomputable def fixedProductSumGapIntegralRegretBoundReal
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real) : Real :=
  ETC.fixedProductBadGapIntegralRegretBoundReal
    spec model baseCommitArm r
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a))
      lo hi

/--
Named Real RHS for the fixed product-coordinate max-gap Bochner ETC regret
wrapper.

This is the max-gap specialization of
`fixedProductBadGapIntegralRegretBoundReal`; it removes the explicit
`badGapBound` parameter while keeping the same finite-product wrong-commit
tail budget.
-/
noncomputable def fixedProductMaxGapIntegralRegretBoundReal
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real) : Real :=
  ETC.fixedProductBadGapIntegralRegretBoundReal
    spec model baseCommitArm r model.maxGap lo hi

/--
Concrete lower-integral ETC regret assembly for the finite argmax commit oracle
under an infinite product reward-coordinate law.

The empirical means are computed from the fixed exploration trace determined by
`baseCommitArm`; the post-exploration action trace commits to the argmax oracle
choice computed from those empirical means.  The suffix term is charged by an
explicit non-best gap bound and the compiled infinite-product wrong-commit
probability bound.
-/
theorem lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (badGapBound : Rat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (hbadGap :
      forall a : Fin K, (a = model.bestArm -> False) ->
        model.gap a <= badGapBound)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.lintegral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec
                ((ETC.argmaxCommitOracle model.hK).choose
                  (fun a : Fin K =>
                    ETC.empMeanAtExploration spec baseCommitArm omega a)))
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ENNReal.ofReal
      (((((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    ENNReal.ofReal
      ((((((r : Nat) : Rat) * badGapBound : Rat) : Real))) *
      ((Finset.univ : Finset (Fin K)).filter
        (fun a : Fin K => a = model.bestArm -> False)).sum
        (ETC.centeredDiffSubGaussianTail spec model
          (ETC.centeredPairwiseRewardDiffVarianceProxy spec model baseCommitArm
            (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  let commit : RewardTrace Rat -> Fin K :=
    fun omega : RewardTrace Rat =>
      (ETC.argmaxCommitOracle model.hK).choose
        (fun a : Fin K =>
          ETC.empMeanAtExploration spec baseCommitArm omega a)
  let pWrong : ENNReal :=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model baseCommitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))
  have hmeas_coord :
      forall a : Fin K,
        Measurable (fun omega : RewardTrace Rat =>
          (fun b : Fin K =>
            ETC.empMeanAtExploration spec baseCommitArm omega b) a) := by
    exact
      ETC.measurable_empMeanAtExploration_coordinates
        (spec := spec)
        (commitArm := baseCommitArm)
        (reward := fun omega : RewardTrace Rat => omega)
        (hreward := by
          intro t
          exact measurable_pi_apply t)
  have hmeas_wrong :
      MeasurableSet {omega : RewardTrace Rat |
        commit omega = model.bestArm -> False} := by
    simpa [commit] using
      (ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean
        (model := model)
        (oracle := ETC.argmaxCommitOracle model.hK)
        (empMean := fun omega : RewardTrace Rat =>
          fun a : Fin K =>
            ETC.empMeanAtExploration spec baseCommitArm omega a)
        hmeas_coord)
  have hprob_wrong :
      MeasureTheory.Measure.infinitePi coordLaw
        {omega : RewardTrace Rat | commit omega = model.bestArm -> False} <=
      pWrong := by
    simpa [commit, pWrong] using
      (ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean
        (hK := model.hK)
        (coordLaw := coordLaw)
        (spec := spec)
        (model := model)
        (commitArm := baseCommitArm)
        (lo := lo)
        (hi := hi)
        (hexplorationPulls_pos := hexplorationPulls_pos)
        (h_coord_bound := h_coord_bound)
        (h_coord_mean := h_coord_mean))
  simpa [commit, pWrong] using
    (ETC.lintegral_ofReal_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob
      (mu := MeasureTheory.Measure.infinitePi coordLaw)
      (spec := spec)
      (model := model)
      (commit := commit)
      (r := r)
      (badGapBound := badGapBound)
      (pWrong := pWrong)
      (hbadGap := hbadGap)
      (hmeas_wrong := hmeas_wrong)
      (hprob_wrong := hprob_wrong))

/--
Concrete Bochner/Real ETC regret assembly for the finite argmax commit oracle
under an infinite product reward-coordinate law.

This is the Real-valued counterpart of
`lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean`.
It uses the same infinite-product wrong-commit probability source, converts
that probability budget with `ENNReal.toReal`, and discharges the abstract
integrability side condition from the measurable finite-valued commit selector.
-/
theorem integral_real_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (badGapBound : Rat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (hbadGap :
      forall a : Fin K, (a = model.bestArm -> False) ->
        model.gap a <= badGapBound)
    (hbadGap_nonneg : (0 : Rat) <= badGapBound)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.integral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        (((pseudoRegret model
            (ETC.fixedProductArgmaxAction spec model baseCommitArm omega)
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ETC.fixedProductBadGapIntegralRegretBoundReal
      spec model baseCommitArm r badGapBound lo hi := by
  let commit : RewardTrace Rat -> Fin K :=
    fun omega : RewardTrace Rat =>
      (ETC.argmaxCommitOracle model.hK).choose
        (fun a : Fin K =>
          ETC.empMeanAtExploration spec baseCommitArm omega a)
  let pWrong : ENNReal :=
    ETC.fixedProductWrongCommitTailBudget spec model baseCommitArm lo hi
  let pWrongReal : Real := pWrong.toReal
  have hmeas_coord :
      forall a : Fin K,
        Measurable (fun omega : RewardTrace Rat =>
          (fun b : Fin K =>
            ETC.empMeanAtExploration spec baseCommitArm omega b) a) := by
    exact
      ETC.measurable_empMeanAtExploration_coordinates
        (spec := spec)
        (commitArm := baseCommitArm)
        (reward := fun omega : RewardTrace Rat => omega)
        (hreward := by
          intro t
          exact measurable_pi_apply t)
  have hmeas_commit : Measurable commit := by
    simpa [commit] using
      (ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
        (oracle := ETC.argmaxCommitOracle model.hK)
        (empMean := fun omega : RewardTrace Rat =>
          fun a : Fin K =>
            ETC.empMeanAtExploration spec baseCommitArm omega a)
        hmeas_coord)
  have hmeas_wrong :
      MeasurableSet {omega : RewardTrace Rat |
        commit omega = model.bestArm -> False} := by
    simpa [commit] using
      (ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean
        (model := model)
        (oracle := ETC.argmaxCommitOracle model.hK)
        (empMean := fun omega : RewardTrace Rat =>
          fun a : Fin K =>
            ETC.empMeanAtExploration spec baseCommitArm omega a)
        hmeas_coord)
  have hprob_wrong :
      MeasureTheory.Measure.infinitePi coordLaw
        {omega : RewardTrace Rat | commit omega = model.bestArm -> False} <=
      pWrong := by
    simpa [commit, pWrong] using
      (ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean
        (hK := model.hK)
        (coordLaw := coordLaw)
        (spec := spec)
        (model := model)
        (commitArm := baseCommitArm)
        (lo := lo)
        (hi := hi)
        (hexplorationPulls_pos := hexplorationPulls_pos)
        (h_coord_bound := h_coord_bound)
        (h_coord_mean := h_coord_mean))
  have hpWrong_ne_none : Not (pWrong = (none : ENNReal)) := by
    simp [pWrong, ETC.fixedProductWrongCommitTailBudget,
      ETC.centeredDiffSubGaussianTail]
  have hprob_wrong_real :
      (MeasureTheory.Measure.infinitePi coordLaw).real
        {omega : RewardTrace Rat | commit omega = model.bestArm -> False} <=
      pWrongReal := by
    simpa [MeasureTheory.Measure.real, pWrongReal] using
      (ENNReal.toReal_mono (by simpa using hpWrong_ne_none) hprob_wrong)
  have hinteg :
      MeasureTheory.Integrable
        (fun omega : RewardTrace Rat =>
          (((pseudoRegret model (ETC.actionWithCommit spec (commit omega))
            (spec.explorationPulls * K + r) : Rat) : Real)))
        (MeasureTheory.Measure.infinitePi coordLaw) :=
    ETC.integrable_real_pseudoRegret_actionWithCommit_choice_of_measurable_commit
      (mu := MeasureTheory.Measure.infinitePi coordLaw)
      (spec := spec)
      (model := model)
      (commit := commit)
      (r := r)
      (hmeas_commit := hmeas_commit)
  simpa [commit, pWrong, pWrongReal,
    ETC.fixedProductBadGapIntegralRegretBoundReal,
    ETC.fixedProductWrongCommitTailBudgetReal] using
    (ETC.integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob
      (mu := MeasureTheory.Measure.infinitePi coordLaw)
      (spec := spec)
      (model := model)
      (commit := commit)
      (r := r)
      (badGapBound := badGapBound)
      (pWrong := pWrongReal)
      (hbadGap := hbadGap)
      (hbadGap_nonneg := hbadGap_nonneg)
      (hmeas_wrong := hmeas_wrong)
      (hprob_wrong := hprob_wrong_real)
      (hinteg := hinteg))

/--
Conservative concrete Bochner/Real ETC regret assembly using the total sum of
model gaps as the suffix bad-gap bound.

This is the Real-valued counterpart of the existing sum-gap `ENNReal.ofReal`
lower-integral adapter.  It removes the explicit `badGapBound` and `hbadGap`
contracts from the concrete fixed-product expected-regret theorem by using
gap nonnegativity over the finite arm set.
-/
theorem integral_real_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_sumGap_prob_of_infinitePi_bounded_actionMean
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.integral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        (((pseudoRegret model
            (ETC.actionWithCommit spec
              ((ETC.argmaxCommitOracle model.hK).choose
                (fun a : Fin K =>
                  ETC.empMeanAtExploration spec baseCommitArm omega a)))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ETC.fixedProductSumGapIntegralRegretBoundReal
      spec model baseCommitArm r lo hi := by
  simpa [ETC.fixedProductArgmaxAction, ETC.fixedProductArgmaxCommit,
    ETC.fixedProductSumGapIntegralRegretBoundReal] using
    (ETC.integral_real_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean
      (coordLaw := coordLaw)
      (spec := spec)
      (model := model)
      (baseCommitArm := baseCommitArm)
      (r := r)
      (badGapBound :=
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => model.gap a))
      (lo := lo)
      (hi := hi)
      (hexplorationPulls_pos := hexplorationPulls_pos)
      (hbadGap := by
        intro a _hne
        exact Finset.single_le_sum
          (fun b _ => FiniteBanditModel.gap_nonneg model b)
          (Finset.mem_univ a))
      (hbadGap_nonneg := by
        exact Finset.sum_nonneg
          (fun a _ => FiniteBanditModel.gap_nonneg model a))
      (h_coord_bound := h_coord_bound)
      (h_coord_mean := h_coord_mean))

/--
Polished fixed-product sum-gap Bochner/Real ETC regret wrapper.

The statement names both the argmax-commit action trace and the conservative
Real-valued sum-gap RHS budget, while remaining on the fixed product-coordinate,
fixed-exploration surface.
-/
theorem integral_real_pseudoRegret_fixedProductArgmaxAction_le_fixedProductSumGapIntegralRegretBoundReal_of_infinitePi_bounded_actionMean
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.integral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        (((pseudoRegret model
            (ETC.fixedProductArgmaxAction spec model baseCommitArm omega)
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ETC.fixedProductSumGapIntegralRegretBoundReal
      spec model baseCommitArm r lo hi := by
  simpa [ETC.fixedProductArgmaxAction, ETC.fixedProductArgmaxCommit] using
    (ETC.integral_real_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_sumGap_prob_of_infinitePi_bounded_actionMean
      (coordLaw := coordLaw)
      (spec := spec)
      (model := model)
      (baseCommitArm := baseCommitArm)
      (r := r)
      (lo := lo)
      (hi := hi)
      (hexplorationPulls_pos := hexplorationPulls_pos)
      (h_coord_bound := h_coord_bound)
      (h_coord_mean := h_coord_mean))

/--
Sharper concrete Bochner/Real ETC regret assembly using
`FiniteBanditModel.maxGap` as the suffix bad-gap bound.

This is the Real-valued counterpart of the existing max-gap `ENNReal.ofReal`
lower-integral adapter.  It removes the explicit `badGapBound` and `hbadGap`
contracts from the concrete fixed-product expected-regret theorem by using the
compiled finite-model max-gap invariants.
-/
theorem integral_real_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.integral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        (((pseudoRegret model
            (ETC.actionWithCommit spec
              ((ETC.argmaxCommitOracle model.hK).choose
                (fun a : Fin K =>
                  ETC.empMeanAtExploration spec baseCommitArm omega a)))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ETC.fixedProductMaxGapIntegralRegretBoundReal
      spec model baseCommitArm r lo hi := by
  simpa [ETC.fixedProductArgmaxAction, ETC.fixedProductArgmaxCommit,
    ETC.fixedProductMaxGapIntegralRegretBoundReal] using
    (ETC.integral_real_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean
      (coordLaw := coordLaw)
      (spec := spec)
      (model := model)
      (baseCommitArm := baseCommitArm)
      (r := r)
      (badGapBound := model.maxGap)
      (lo := lo)
      (hi := hi)
      (hexplorationPulls_pos := hexplorationPulls_pos)
      (hbadGap := by
        intro a _hne
        exact FiniteBanditModel.gap_le_maxGap model a)
      (hbadGap_nonneg := FiniteBanditModel.maxGap_nonneg model)
      (h_coord_bound := h_coord_bound)
      (h_coord_mean := h_coord_mean))

/--
Polished fixed-product max-gap Bochner/Real ETC regret wrapper.

The statement names both the argmax-commit action trace and the Real-valued RHS
budget, while remaining on the fixed product-coordinate, fixed-exploration
surface.
-/
theorem integral_real_pseudoRegret_fixedProductArgmaxAction_le_fixedProductMaxGapIntegralRegretBoundReal_of_infinitePi_bounded_actionMean
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.integral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        (((pseudoRegret model
            (ETC.fixedProductArgmaxAction spec model baseCommitArm omega)
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ETC.fixedProductMaxGapIntegralRegretBoundReal
      spec model baseCommitArm r lo hi := by
  simpa [ETC.fixedProductArgmaxAction, ETC.fixedProductArgmaxCommit] using
    (ETC.integral_real_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean
      (coordLaw := coordLaw)
      (spec := spec)
      (model := model)
      (baseCommitArm := baseCommitArm)
      (r := r)
      (lo := lo)
      (hi := hi)
      (hexplorationPulls_pos := hexplorationPulls_pos)
      (h_coord_bound := h_coord_bound)
      (h_coord_mean := h_coord_mean))

/--
Conservative concrete lower-integral ETC regret assembly using the total sum
of model gaps as the suffix bad-gap bound.

This removes the explicit `badGapBound`/`hbadGap` contract from the concrete
infinite-product wrapper.  The price is a looser suffix constant:
`sum_a model.gap a` bounds every non-best gap by nonnegativity.
-/
theorem lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_sumGap_prob_of_infinitePi_bounded_actionMean
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.lintegral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec
                ((ETC.argmaxCommitOracle model.hK).choose
                  (fun a : Fin K =>
                    ETC.empMeanAtExploration spec baseCommitArm omega a)))
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ENNReal.ofReal
      (((((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    ENNReal.ofReal
      ((((((r : Nat) : Rat) *
        ((Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => model.gap a)) : Rat) : Real))) *
      ((Finset.univ : Finset (Fin K)).filter
        (fun a : Fin K => a = model.bestArm -> False)).sum
        (ETC.centeredDiffSubGaussianTail spec model
          (ETC.centeredPairwiseRewardDiffVarianceProxy spec model baseCommitArm
            (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean
      (coordLaw := coordLaw)
      (spec := spec)
      (model := model)
      (baseCommitArm := baseCommitArm)
      (r := r)
      (badGapBound :=
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => model.gap a))
      (lo := lo)
      (hi := hi)
      (hexplorationPulls_pos := hexplorationPulls_pos)
      (hbadGap := by
        intro a _hne
        exact Finset.single_le_sum
          (fun b _ => FiniteBanditModel.gap_nonneg model b)
          (Finset.mem_univ a))
      (h_coord_bound := h_coord_bound)
      (h_coord_mean := h_coord_mean)

/--
Sharper concrete lower-integral ETC regret assembly using
`FiniteBanditModel.maxGap` as the suffix bad-gap bound.

This keeps the same infinite-product wrong-commit probability term as the
sum-gap wrapper, but charges each wrong suffix pull by the maximum local gap
instead of the total sum of all gaps.
-/
theorem lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.lintegral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec
                ((ETC.argmaxCommitOracle model.hK).choose
                  (fun a : Fin K =>
                    ETC.empMeanAtExploration spec baseCommitArm omega a)))
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ENNReal.ofReal
      (((((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    ENNReal.ofReal
      ((((((r : Nat) : Rat) * model.maxGap : Rat) : Real))) *
      ((Finset.univ : Finset (Fin K)).filter
        (fun a : Fin K => a = model.bestArm -> False)).sum
        (ETC.centeredDiffSubGaussianTail spec model
          (ETC.centeredPairwiseRewardDiffVarianceProxy spec model baseCommitArm
            (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean
      (coordLaw := coordLaw)
      (spec := spec)
      (model := model)
      (baseCommitArm := baseCommitArm)
      (r := r)
      (badGapBound := model.maxGap)
      (lo := lo)
      (hi := hi)
      (hexplorationPulls_pos := hexplorationPulls_pos)
      (hbadGap := by
        intro a _hne
        exact FiniteBanditModel.gap_le_maxGap model a)
      (h_coord_bound := h_coord_bound)
      (h_coord_mean := h_coord_mean)

/--
Polished fixed-product max-gap lower-integral ETC regret wrapper.

The statement names both the argmax-commit action trace and the RHS max-gap
budget, while remaining exactly on the same fixed product-coordinate,
fixed-exploration, `ENNReal.ofReal` surface as the concrete max-gap assembly.
-/
theorem lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductMaxGapLintegralRegretBound_of_infinitePi_bounded_actionMean
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.lintegral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.fixedProductArgmaxAction spec model baseCommitArm omega)
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ETC.fixedProductMaxGapLintegralRegretBound spec model baseCommitArm r lo hi := by
  simpa [ETC.fixedProductArgmaxAction, ETC.fixedProductArgmaxCommit,
    ETC.fixedProductMaxGapLintegralRegretBound] using
    (ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean
      (coordLaw := coordLaw)
      (spec := spec)
      (model := model)
      (baseCommitArm := baseCommitArm)
      (r := r)
      (lo := lo)
      (hi := hi)
      (hexplorationPulls_pos := hexplorationPulls_pos)
      (h_coord_bound := h_coord_bound)
      (h_coord_mean := h_coord_mean))

end ETC
end BanditRLProof
