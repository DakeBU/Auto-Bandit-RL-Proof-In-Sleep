import BanditRLProof.Exp3RealizedRegret
import BanditRLProof.ConditionalExpectationReward
import BanditRLProof.ConcentrationSubGaussian

/-!
# EXP3 realized-loss concentration

This module identifies the successor action law inside `condExpKernel` without
requiring a countable ambient action type.  It then freezes the predictable
environment/history coordinates and applies the bounded centered Hoeffding MGF
bound to the selected and realized one-step loss deviations.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v w

theorem condExpKernel_map_eq_finiteActionMeasure_of_condDistrib_ae_eq
    {Omega : Type u} {Condition : Type v} {Action : Type w}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Nonempty Omega]
    [mCondition : MeasurableSpace Condition]
    [mAction : MeasurableSpace Action] [StandardBorelSpace Action]
    [MeasurableSingletonClass Action] [Nonempty Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : Omega -> Action) (Y : Omega -> Condition)
    (hX : @Measurable Omega Action mOmega mAction X)
    (hY : @Measurable Omega Condition mOmega mCondition Y)
    (arms : Finset Action) (prob : Condition -> Action -> Real)
    (source : MeasurableFiniteActionDistribution arms prob)
    (hcond :
      Filter.EventuallyEq (ae (mu.map Y))
        (condDistrib X Y mu)
        (finiteActionKernel arms prob source)) :
    Filter.Eventually
      (fun omega =>
        @Measure.map Omega Action mOmega mAction X
            (@condExpKernel Omega mOmega _ mu _ (mCondition.comap Y) omega) =
          finiteActionMeasure arms (prob (Y omega)))
      (ae (mu.trim hY.comap_le)) := by
  have hcond_pullback :
      Filter.Eventually
        (fun omega =>
          condDistrib X Y mu (Y omega) =
            finiteActionKernel arms prob source (Y omega))
        (ae mu) :=
    ae_of_ae_map hY.aemeasurable hcond
  have hsingle (action : Action) (haction : action ∈ arms) :
      Filter.EventuallyEq (ae (mu.trim hY.comap_le))
        (fun omega =>
          (@Measure.map Omega Action mOmega mAction X
            (@condExpKernel Omega mOmega _ mu _ (mCondition.comap Y) omega))
              {action})
        (fun omega => finiteActionMeasure arms (prob (Y omega)) {action}) := by
    have hevent :
        Filter.EventuallyEq (ae mu)
          (fun omega => condDistrib X Y mu (Y omega) {action})
          (fun omega =>
            (@condExpKernel Omega mOmega _ mu _
              (mCondition.comap Y)).map X omega {action}) :=
      condDistrib_apply_ae_eq_condExpKernel_map
        (μ := mu) hX hY (MeasurableSet.singleton action)
    have hambient :
        Filter.EventuallyEq (ae mu)
          (fun omega =>
            (@Measure.map Omega Action mOmega mAction X
              (@condExpKernel Omega mOmega _ mu _ (mCondition.comap Y) omega))
                {action})
          (fun omega => finiteActionMeasure arms (prob (Y omega)) {action}) := by
      filter_upwards [hevent, hcond_pullback] with omega hevent_eq hcond_eq
      calc
        (@Measure.map Omega Action mOmega mAction X
            (@condExpKernel Omega mOmega _ mu _ (mCondition.comap Y) omega))
              {action} =
            ((@condExpKernel Omega mOmega _ mu _
              (mCondition.comap Y)).map X omega) {action} := by
                rw [Kernel.map_apply _ hX]
        _ =
            condDistrib X Y mu (Y omega) {action} := hevent_eq.symm
        _ = finiteActionKernel arms prob source (Y omega) {action} := by
          rw [hcond_eq]
        _ = finiteActionMeasure arms (prob (Y omega)) {action} := rfl
    have hlhs :
        @Measurable Omega ENNReal (mCondition.comap Y) inferInstance
          (fun omega =>
            (@Measure.map Omega Action mOmega mAction X
              (@condExpKernel Omega mOmega _ mu _ (mCondition.comap Y) omega))
                {action}) := by
      have h :=
        ((@condExpKernel Omega mOmega _ mu _ (mCondition.comap Y)).map X).measurable_coe
          (MeasurableSet.singleton action)
      simpa [Kernel.map_apply _ hX] using h
    have hrhs :
        @Measurable Omega ENNReal (mCondition.comap Y) inferInstance
          (fun omega => finiteActionMeasure arms (prob (Y omega)) {action}) := by
      have h :=
        (finiteActionKernel arms prob source).measurable_coe
          (MeasurableSet.singleton action)
      simpa [finiteActionKernel_apply] using
        h.comp (Measurable.of_comap_le le_rfl)
    exact ae_eq_trim_of_measurable hY.comap_le hlhs hrhs hambient
  have hall :
      Filter.Eventually
        (fun omega => forall action, action ∈ arms ->
          (@Measure.map Omega Action mOmega mAction X
            (@condExpKernel Omega mOmega _ mu _ (mCondition.comap Y) omega))
              {action} =
            finiteActionMeasure arms (prob (Y omega)) {action})
        (ae (mu.trim hY.comap_le)) :=
    (Filter.eventually_all_finset arms).2 hsingle
  filter_upwards [hall] with omega hall_omega
  let nu : Measure Action :=
    @Measure.map Omega Action mOmega mAction X
      (@condExpKernel Omega mOmega _ mu _ (mCondition.comap Y) omega)
  let condMu : Measure Omega :=
    @condExpKernel Omega mOmega _ mu _ (mCondition.comap Y) omega
  letI : IsProbabilityMeasure condMu := by
    dsimp [condMu]
    infer_instance
  letI : IsProbabilityMeasure nu := by
    change IsProbabilityMeasure (@Measure.map Omega Action mOmega mAction X condMu)
    exact Measure.isProbabilityMeasure_map hX.aemeasurable
  have htarget_arms :
      finiteActionMeasure arms (prob (Y omega)) (arms : Set Action) = 1 := by
    simp only [finiteActionMeasure, Measure.finset_sum_apply,
      Measure.smul_apply, smul_eq_mul, Measure.dirac_apply]
    calc
      ∑ action ∈ arms,
          ENNReal.ofReal (prob (Y omega) action) *
            (arms : Set Action).indicator 1 action =
          ∑ action ∈ arms, ENNReal.ofReal (prob (Y omega) action) := by
        apply Finset.sum_congr rfl
        intro action haction
        simp [haction]
      _ = ENNReal.ofReal (∑ action ∈ arms, prob (Y omega) action) := by
        rw [ENNReal.ofReal_sum_of_nonneg
          (source.distribution (Y omega)).nonneg]
      _ = 1 := by
        rw [(source.distribution (Y omega)).sum_eq_one]
        simp
  have hnu_arms : nu (arms : Set Action) = 1 := by
    rw [← sum_measure_singleton]
    calc
      ∑ action ∈ arms, nu {action} =
          ∑ action ∈ arms,
            finiteActionMeasure arms (prob (Y omega)) {action} := by
        apply Finset.sum_congr rfl
        intro action haction
        exact hall_omega action haction
      _ = finiteActionMeasure arms (prob (Y omega)) (arms : Set Action) :=
        sum_measure_singleton
      _ = 1 := htarget_arms
  have hnu_mem : Filter.Eventually (fun action => action ∈ arms) (ae nu) := by
    change {action : Action | action ∈ arms} ∈ ae nu
    rw [mem_ae_iff]
    exact (prob_compl_eq_zero_iff (by measurability)).2 hnu_arms
  calc
    nu = ∑ action ∈ arms, nu {action} • Measure.dirac action :=
      Measure.ae_mem_finset_iff.mp hnu_mem
    _ = finiteActionMeasure arms (prob (Y omega)) := by
      rw [finiteActionMeasure]
      apply Finset.sum_congr rfl
      intro action haction
      rw [hall_omega action haction]
      have htarget_singleton :
          finiteActionMeasure arms (prob (Y omega)) {action} =
            ENNReal.ofReal (prob (Y omega) action) := by
        simp only [finiteActionMeasure, Measure.finset_sum_apply,
          Measure.smul_apply, smul_eq_mul, Measure.dirac_apply]
        rw [Finset.sum_eq_single action]
        · simp
        · intro other hother hne
          simp [hne]
        · exact fun hnot => (hnot haction).elim
      rw [htarget_singleton]

/-- Selected predictable loss minus its exploration-mixed conditional mean. -/
noncomputable def sampledTrajectorySelectedDeviationAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  predictableLossAt loss t sample (sample.2 t).1 -
    sampledTrajectoryExploredPredictableLossAt arms eta gamma loss t sample

theorem measurable_sampledTrajectorySelectedDeviationAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    Measurable (sampledTrajectorySelectedDeviationAt
      arms eta gamma loss t) := by
  exact (measurable_sampledTrajectorySelectedPredictableLossAt loss t).sub
    (measurable_sampledTrajectoryExploredPredictableLossAt
      arms harms eta gamma hgamma_nonneg hgamma_le_one loss t)

theorem sampledPredictableSelectedDeviation_succ_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
      (sample.1, Preorder.frestrictLe n sample.2)
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace
        (Env × History.FinitePairHistory Action Real n)).comap history)
      (measurable_fst.prodMk
        ((Preorder.measurable_frestrictLe n).comp measurable_snd)).comap_le
      (sampledTrajectorySelectedDeviationAt arms eta gamma loss (n + 1))
      (Concentration.intervalVarianceProxy 0 1) mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.1, Preorder.frestrictLe n sample.2)
  have hhistory : Measurable history :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.2 (n + 1)).1
  let prob := fun input : Env × History.FinitePairHistory Action Real n =>
    sampledHistoryDistribution arms eta gamma n input.2
  let roundLoss := fun input : Env × History.FinitePairHistory Action Real n =>
    loss.successor n input.1 input.2
  let mean := fun input : Env × History.FinitePairHistory Action Real n =>
    arms.sum (fun selected => prob input selected * roundLoss input selected)
  let source := sampledEnvironmentHistoryDistributionSource
    (Env := Env) arms harms eta gamma hgamma_nonneg hgamma_le_one n
  let mcond := (inferInstance : MeasurableSpace
    (Env × History.FinitePairHistory Action Real n)).comap history
  letI : MeasurableSpace (Env × ((k : Nat) -> Action × Real)) :=
    Prod.instMeasurableSpace
  let X := sampledTrajectorySelectedDeviationAt
    arms eta gamma loss (n + 1)
  let target : (Env × ((k : Nat) -> Action × Real)) -> Measure Real :=
    fun omega => Measure.map
      (fun selected => roundLoss (history omega) selected - mean (history omega))
      (finiteActionMeasure arms (prob (history omega)))
  have haction : Measurable action := by fun_prop
  have hmcond : mcond <= Prod.instMeasurableSpace := hhistory.comap_le
  have hX : Measurable X := by
    simpa [X] using
      (measurable_sampledTrajectorySelectedDeviationAt
        arms harms eta gamma hgamma_nonneg hgamma_le_one loss (n + 1))
  have hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source := by
    simpa [mu, history, action, prob, source] using
      (sampledImportanceWeightedTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss n)
  have haction_map :=
    condExpKernel_map_eq_finiteActionMeasure_of_condDistrib_ae_eq
      mu action history haction hhistory arms prob source hcond
  have hhistory_mcond :
      @Measurable (Env × ((k : Nat) -> Action × Real))
        (Env × History.FinitePairHistory Action Real n)
        mcond inferInstance history := Measurable.of_comap_le le_rfl
  have hhistory_map :=
    ConditionalExpectationReward.condExpKernel_map_eq_dirac_of_measurable
      mu mcond hmcond history hhistory_mcond
  have hhistory_ae :
      Filter.Eventually
        (fun omega => Filter.EventuallyEq
          (ae (@condExpKernel
            (Env × ((k : Nat) -> Action × Real)) inferInstance _ mu _ mcond omega))
          history (fun _ => history omega))
        (ae (mu.trim hmcond)) := by
    filter_upwards [hhistory_map] with omega hmap
    exact ConditionalExpectationReward.eventuallyEq_const_of_map_eq_dirac
      (@condExpKernel
        (Env × ((k : Nat) -> Action × Real)) inferInstance _ mu _ mcond omega)
      history (history omega) hhistory hmap
  have hkernel_X_eq :
      Filter.Eventually
        (fun omega => Filter.EventuallyEq
          (ae (@condExpKernel
            (Env × ((k : Nat) -> Action × Real)) inferInstance _ mu _ mcond omega))
          X
          (fun y => roundLoss (history omega) (action y) - mean (history omega)))
        (ae (mu.trim hmcond)) := by
    filter_upwards [hhistory_ae] with omega hfreeze
    filter_upwards [hfreeze] with y hy
    change roundLoss (history y) (action y) - mean (history y) =
      roundLoss (history omega) (action y) - mean (history omega)
    rw [hy]
  have hkernel_map :
      Filter.Eventually
        (fun omega =>
          @Measure.map (Env × ((k : Nat) -> Action × Real)) Real inferInstance inferInstance
            X (@condExpKernel
              (Env × ((k : Nat) -> Action × Real)) inferInstance _ mu _ mcond omega) =
            target omega)
        (ae (mu.trim hmcond)) := by
    filter_upwards [haction_map, hkernel_X_eq] with omega haction_eq hXeq
    let score : Action -> Real :=
      fun selected => roundLoss (history omega) selected - mean (history omega)
    have hscore : Measurable score := by
      exact ((loss.measurable_successor n).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).sub
          measurable_const
    calc
      @Measure.map (Env × ((k : Nat) -> Action × Real)) Real inferInstance inferInstance
          X (@condExpKernel
            (Env × ((k : Nat) -> Action × Real)) inferInstance _ mu _ mcond omega) =
        @Measure.map (Env × ((k : Nat) -> Action × Real)) Real inferInstance inferInstance
          (fun y => score (action y))
          (@condExpKernel
            (Env × ((k : Nat) -> Action × Real)) inferInstance _ mu _ mcond omega) :=
          Measure.map_congr hXeq
      _ = Measure.map score
          (@Measure.map (Env × ((k : Nat) -> Action × Real)) Action inferInstance inferInstance
            action (@condExpKernel
              (Env × ((k : Nat) -> Action × Real)) inferInstance _ mu _ mcond omega)) := by
            rw [Measure.map_map hscore haction]
            congr 1
      _ = target omega := by
        rw [haction_eq]
  have htarget_subG :
      Filter.Eventually
        (fun omega => HasSubgaussianMGF (fun z : Real => z)
          (Concentration.intervalVarianceProxy 0 1) (target omega))
        (ae (mu.trim hmcond)) := by
    filter_upwards [] with omega
    let actionMu := finiteActionMeasure arms (prob (history omega))
    let raw := roundLoss (history omega)
    let score : Action -> Real := fun selected => raw selected - mean (history omega)
    letI : IsProbabilityMeasure actionMu :=
      finiteActionMeasure_isProbabilityMeasure arms (prob (history omega))
        (source.distribution (history omega))
    have hraw : Measurable raw := by
      exact (loss.measurable_successor n).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hbound : Filter.Eventually
        (fun selected => raw selected ∈ Set.Icc (0 : Real) 1) (ae actionMu) :=
      Filter.Eventually.of_forall fun selected =>
        loss.successor_mem_unitInterval n (history omega).1
          (history omega).2 selected
    have hmean : integral actionMu raw = mean (history omega) := by
      simpa [actionMu, raw, mean] using
        (integral_finiteActionMeasure_eq_sum arms (prob (history omega))
          (source.distribution (history omega)) raw)
    have hsub : HasSubgaussianMGF score
        (Concentration.intervalVarianceProxy 0 1) actionMu := by
      simpa [score, raw] using
        (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
          actionMu hraw.aemeasurable hbound hmean)
    have hscore : Measurable score := hraw.sub measurable_const
    apply (HasSubgaussianMGF.id_map_iff hscore.aemeasurable).2
    simpa [target, actionMu, score, raw] using hsub
  exact ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq
    mu mcond hmcond X (Concentration.intervalVarianceProxy 0 1)
      hX target hkernel_map htarget_subG

noncomputable def sampledTrajectoryRealizedDeviationAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  sampledTrajectoryRealizedLossAt t sample -
    sampledTrajectoryExploredPredictableLossAt arms eta gamma loss t sample

theorem sampledPredictableRealizedDeviation_succ_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (n : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
      (sample.1, Preorder.frestrictLe n sample.2)
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace
        (Env × History.FinitePairHistory Action Real n)).comap history)
      (measurable_fst.prodMk
        ((Preorder.measurable_frestrictLe n).comp measurable_snd)).comap_le
      (sampledTrajectoryRealizedDeviationAt arms eta gamma loss (n + 1))
      (Concentration.intervalVarianceProxy 0 1) mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.1, Preorder.frestrictLe n sample.2)
  have hhistory : Measurable history :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  let mcond := (inferInstance : MeasurableSpace
    (Env × History.FinitePairHistory Action Real n)).comap history
  letI : MeasurableSpace (Env × ((k : Nat) -> Action × Real)) :=
    Prod.instMeasurableSpace
  have hmcond : mcond <= Prod.instMeasurableSpace := hhistory.comap_le
  have hselected :=
    sampledPredictableSelectedDeviation_succ_hasCondSubgaussianMGF
      prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss n
  dsimp only at hselected
  have hreward :=
    sampledTrajectoryRealizedLossAt_ae_eq_selectedPredictable
      prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss (n + 1)
  dsimp only at hreward
  have hdeviation :
      sampledTrajectorySelectedDeviationAt arms eta gamma loss (n + 1) =ᵐ[mu]
        sampledTrajectoryRealizedDeviationAt arms eta gamma loss (n + 1) := by
    filter_upwards [hreward] with sample hs
    simp only [sampledTrajectorySelectedDeviationAt,
      sampledTrajectoryRealizedDeviationAt]
    rw [hs]
  change ProbabilityTheory.Kernel.HasSubgaussianMGF
    (sampledTrajectorySelectedDeviationAt arms eta gamma loss (n + 1))
    (Concentration.intervalVarianceProxy 0 1)
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond) at hselected
  change ProbabilityTheory.Kernel.HasSubgaussianMGF
    (sampledTrajectoryRealizedDeviationAt arms eta gamma loss (n + 1))
    (Concentration.intervalVarianceProxy 0 1)
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond)
  apply (ProbabilityTheory.Kernel.HasSubgaussianMGF_congr ?_).1 hselected
  rw [@ProbabilityTheory.condExpKernel_comp_trim
    (Env × ((k : Nat) -> Action × Real)) mcond inferInstance _ mu _ hmcond]
  exact hdeviation

end BanditRLProof.Exp3
