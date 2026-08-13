import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVIBellmanInnovation

/-! Predictable episode-level Bellman innovations on the recurrent source. -/

open MeasureTheory
open scoped ENNReal ProbabilityTheory BigOperators

universe u v w

namespace BanditRLProof

/-- A function with a countable discrete left coordinate is measurable when
every right section is measurable. -/
theorem measurable_prod_of_countable_left
    {Alpha Beta Gamma : Type*}
    [MeasurableSpace Alpha] [MeasurableSpace Beta] [MeasurableSpace Gamma]
    [Countable Alpha] [MeasurableSingletonClass Alpha]
    (f : Alpha × Beta -> Gamma)
    (hf : forall a, Measurable (fun b => f (a, b))) :
    Measurable f := by
  intro s hs
  have hpreimage : f ⁻¹' s =
      ⋃ a : Alpha, ({a} : Set Alpha) ×ˢ
        ((fun b => f (a, b)) ⁻¹' s) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod,
      Set.mem_singleton_iff]
    constructor
    · intro hp
      exact ⟨p.1, rfl, hp⟩
    · rintro ⟨a, ha, hp⟩
      subst a
      exact hp
  rw [hpreimage]
  exact MeasurableSet.iUnion fun a =>
    MeasurableSet.singleton a |>.prod ((hf a) hs)

end BanditRLProof

namespace MeasureTheory.Measure

/-- Mapping a composition-product by a function which may also read the
conditioning coordinate is the composition-product with the correspondingly
mapped copy-and-kernel law. -/
lemma compProd_map_dependent
    {Alpha : Type u} {Beta : Type v} {Gamma : Type w}
    [MeasurableSpace Alpha] [MeasurableSpace Beta] [MeasurableSpace Gamma]
    (mu : Measure Alpha) [SFinite mu]
    (kappa : ProbabilityTheory.Kernel Alpha Beta)
    [ProbabilityTheory.IsSFiniteKernel kappa]
    (f : Alpha × Beta -> Gamma) (hf : Measurable f) :
    (mu ⊗ₘ kappa).map (fun p => (p.1, f p)) =
      mu ⊗ₘ ((ProbabilityTheory.Kernel.id ×ₖ kappa).map f) := by
  ext s hs
  rw [Measure.map_apply (measurable_fst.prodMk hf) hs,
    Measure.compProd_apply
      (hs.preimage (measurable_fst.prodMk hf)),
    Measure.compProd_apply hs]
  congr with a
  rw [ProbabilityTheory.Kernel.map_apply _ hf]
  rw [ProbabilityTheory.Kernel.prod_apply]
  rw [ProbabilityTheory.Kernel.id_apply, Measure.dirac_prod]
  rw [Measure.map_map hf measurable_prodMk_left]
  rw [Measure.map_apply (hf.comp measurable_prodMk_left)
    (hs.preimage measurable_prodMk_left)]
  rfl

end MeasureTheory.Measure

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveEpisodeBatchSource

/-- Conditional law of a statistic which may depend measurably on both the
observed prefix and the newly generated batch. -/
theorem trajectoryMeasure_condDistrib_historyBatchStatistic
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat)
    (statistic : EpisodeBatchPrefix mdp episodes n ×
      EpisodeBatch mdp episodes -> Real)
    (hstatistic : Measurable statistic) :
    ProbabilityTheory.condDistrib
        (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
          statistic (Preorder.frestrictLe n trajectory, trajectory (n + 1)))
        (Preorder.frestrictLe n) source.trajectoryMeasure =ᵐ[
          source.trajectoryMeasure.map (Preorder.frestrictLe n)]
      ((ProbabilityTheory.Kernel.id ×ₖ source.batchKernel n).map statistic) := by
  let history : EpisodeBatchTrajectory mdp episodes ->
      EpisodeBatchPrefix mdp episodes n := Preorder.frestrictLe n
  let nextBatch : EpisodeBatchTrajectory mdp episodes ->
      EpisodeBatch mdp episodes := fun trajectory => trajectory (n + 1)
  have hnext : AEMeasurable nextBatch source.trajectoryMeasure :=
    (measurable_pi_apply (n + 1)).aemeasurable
  have hpairCond :
      ProbabilityTheory.condDistrib
          (fun trajectory => (history trajectory, nextBatch trajectory))
          history source.trajectoryMeasure =ᵐ[
            source.trajectoryMeasure.map history]
        (ProbabilityTheory.Kernel.id ×ₖ source.batchKernel n) := by
    apply (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
      (μ := source.trajectoryMeasure) history
      ((Preorder.measurable_frestrictLe n).prodMk
        (measurable_pi_apply (n + 1)) |>.aemeasurable)
      (ProbabilityTheory.Kernel.id ×ₖ source.batchKernel n)).2
    have hnextCond := source.trajectoryMeasure_condDistrib n
    have hjoint :
        source.trajectoryMeasure.map
            (fun trajectory => (history trajectory, nextBatch trajectory)) =
          source.trajectoryMeasure.map history ⊗ₘ source.batchKernel n := by
      exact (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
        (μ := source.trajectoryMeasure) history hnext
        (source.batchKernel n)).1 hnextCond
    let duplicate :
        (EpisodeBatchPrefix mdp episodes n × EpisodeBatch mdp episodes) ->
          EpisodeBatchPrefix mdp episodes n ×
            (EpisodeBatchPrefix mdp episodes n × EpisodeBatch mdp episodes) :=
      fun p => (p.1, p)
    calc
      source.trajectoryMeasure.map
          (fun trajectory =>
            (history trajectory, (history trajectory, nextBatch trajectory))) =
        (source.trajectoryMeasure.map
          (fun trajectory => (history trajectory, nextBatch trajectory))).map
            duplicate := by
              rw [Measure.map_map]
              · rfl
              · exact (measurable_fst.prodMk measurable_id)
              · exact (Preorder.measurable_frestrictLe n).prodMk
                  (measurable_pi_apply (n + 1))
      _ = (source.trajectoryMeasure.map history ⊗ₘ source.batchKernel n).map
            duplicate := by rw [hjoint]
      _ = source.trajectoryMeasure.map history ⊗ₘ
          (ProbabilityTheory.Kernel.id ×ₖ source.batchKernel n) := by
            simpa [duplicate] using
              (MeasureTheory.Measure.compProd_map_dependent
                (source.trajectoryMeasure.map history)
                (source.batchKernel n) (fun p => p)
                (measurable_id : Measurable
                  (fun p : EpisodeBatchPrefix mdp episodes n ×
                    EpisodeBatch mdp episodes => p)))
  have hcomp :
      ProbabilityTheory.condDistrib
          (statistic ∘ fun trajectory =>
            (history trajectory, nextBatch trajectory))
          history source.trajectoryMeasure =ᵐ[
            source.trajectoryMeasure.map history]
        (ProbabilityTheory.condDistrib
          (fun trajectory => (history trajectory, nextBatch trajectory))
          history source.trajectoryMeasure).map statistic :=
    ProbabilityTheory.condDistrib_comp
      (μ := source.trajectoryMeasure)
      (Y := fun trajectory => (history trajectory, nextBatch trajectory))
      history
      (((Preorder.measurable_frestrictLe n).prodMk
        (measurable_pi_apply (n + 1))).aemeasurable)
      hstatistic
  filter_upwards [hcomp, hpairCond] with observed hcompAt hpairAt
  rw [ProbabilityTheory.Kernel.map_apply _ hstatistic] at hcompAt
  rw [hpairAt] at hcompAt
  rw [ProbabilityTheory.Kernel.map_apply _ hstatistic]
  simpa [history, nextBatch, Function.comp_def] using hcompAt

/-- Trimmed conditional-expectation-kernel version of the preceding dependent
statistic law. -/
theorem condExpKernel_map_historyBatchStatistic_eq_batchKernel
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (n : Nat)
    (statistic : EpisodeBatchPrefix mdp episodes n ×
      EpisodeBatch mdp episodes -> Real)
    (hstatistic : Measurable statistic) :
    Filter.Eventually
      (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
        Measure.map
            (fun path : EpisodeBatchTrajectory mdp episodes =>
              statistic
                (Preorder.frestrictLe n path, path (n + 1)))
            (ProbabilityTheory.condExpKernel source.trajectoryMeasure
              ((inferInstance : MeasurableSpace
                (EpisodeBatchPrefix mdp episodes n)).comap
                  (Preorder.frestrictLe n)) trajectory) =
          ((ProbabilityTheory.Kernel.id ×ₖ source.batchKernel n).map statistic)
            (Preorder.frestrictLe n trajectory))
      (ae (source.trajectoryMeasure.trim
        (Preorder.measurable_frestrictLe n).comap_le)) := by
  let target :=
    ((ProbabilityTheory.Kernel.id ×ₖ source.batchKernel n).map statistic)
  letI : ProbabilityTheory.IsMarkovKernel target :=
    ProbabilityTheory.Kernel.IsMarkovKernel.map _ hstatistic
  exact
    ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim
      source.trajectoryMeasure
      (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
        statistic (Preorder.frestrictLe n trajectory, trajectory (n + 1)))
      (Preorder.frestrictLe n)
      (hstatistic.comp
        ((Preorder.measurable_frestrictLe n).prodMk
          (measurable_pi_apply (n + 1))))
      (Preorder.measurable_frestrictLe n)
      target
      (source.trajectoryMeasure_condDistrib_historyBatchStatistic
        n statistic hstatistic)

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeHoeffdingUCBVI

/-- Inflation factor generated by the `z/(32H)` self-bounding term. -/
noncomputable def bellmanInflation (mdp : MDP State Action) : Real :=
  1 + 1 / (32 * (mdp.horizon : Real))

/-- Uniform cap for every finite-horizon power of `bellmanInflation`. -/
noncomputable def bellmanWeightCap : Real := 32 / 31

theorem bellmanInflation_one_le
    (mdp : MDP State Action) :
    1 <= bellmanInflation mdp := by
  unfold bellmanInflation
  have : (0 : Real) <= 1 / (32 * (mdp.horizon : Real)) := by positivity
  linarith

theorem bellmanInflation_pow_le_cap
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon) :
    bellmanInflation mdp ^ remaining <= bellmanWeightCap := by
  let x : Real := 1 / (32 * (mdp.horizon : Real))
  have hhorizonReal : 0 < (mdp.horizon : Real) := by exact_mod_cast hhorizon
  have hx : 0 <= x := by dsimp [x]; positivity
  have hbase : bellmanInflation mdp <= Real.exp x := by
    simpa [bellmanInflation, x, add_comm] using Real.add_one_le_exp x
  have hpow : bellmanInflation mdp ^ remaining <= Real.exp x ^ remaining := by
    have hnonneg : 0 <= bellmanInflation mdp := by
      linarith [bellmanInflation_one_le mdp]
    gcongr
  have hremainingReal : (remaining : Real) <= mdp.horizon := by exact_mod_cast hremaining
  have hmul : (remaining : Real) * x <= (1 : Real) / 32 := by
    dsimp [x]
    have hdiv := div_le_div_of_nonneg_right hremainingReal
      (by positivity : (0 : Real) <= 32 * mdp.horizon)
    calc
      (remaining : Real) * (1 / (32 * (mdp.horizon : Real))) =
          (remaining : Real) / (32 * (mdp.horizon : Real)) := by ring
      _ <= (mdp.horizon : Real) / (32 * (mdp.horizon : Real)) := hdiv
      _ = (1 : Real) / 32 := by field_simp
  have hexp : Real.exp x ^ remaining <= Real.exp ((1 : Real) / 32) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr hmul
  have hcap := Real.exp_bound_div_one_sub_of_interval
    (x := (1 : Real) / 32) (by norm_num) (by norm_num)
  calc
    bellmanInflation mdp ^ remaining <= Real.exp x ^ remaining := hpow
    _ <= Real.exp ((1 : Real) / 32) := hexp
    _ <= 1 / (1 - (1 : Real) / 32) := hcap
    _ = bellmanWeightCap := by norm_num [bellmanWeightCap]

/-- Normalized chronological recursion weight.  Multiplication by the global
cap `32/31` later recovers the exact factor `alpha^(stage+1)`. -/
noncomputable def normalizedBellmanWeight
    (mdp : MDP State Action) (stage : Fin mdp.horizon) : Real :=
  (31 / 32 : Real) * bellmanInflation mdp ^ (stage.val + 1)

/-- Weight of the local charge at a chronological stage. -/
noncomputable def normalizedBellmanChargeWeight
    (mdp : MDP State Action) (stage : Fin mdp.horizon) : Real :=
  (31 / 32 : Real) * bellmanInflation mdp ^ stage.val

theorem normalizedBellmanChargeWeight_mem_Icc
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (stage : Fin mdp.horizon) :
    normalizedBellmanChargeWeight mdp stage ∈ Set.Icc (0 : Real) 1 := by
  have hpow := bellmanInflation_pow_le_cap mdp hhorizon stage.val
    (Nat.le_of_lt stage.isLt)
  have hpowNonneg : 0 <= bellmanInflation mdp ^ stage.val := by
    have : 0 <= bellmanInflation mdp := by
      linarith [bellmanInflation_one_le mdp]
    positivity
  constructor
  · unfold normalizedBellmanChargeWeight
    positivity
  · unfold normalizedBellmanChargeWeight
    have hscale : (0 : Real) <= 31 / 32 := by norm_num
    calc
      (31 / 32 : Real) * bellmanInflation mdp ^ stage.val <=
          (31 / 32 : Real) * bellmanWeightCap :=
        mul_le_mul_of_nonneg_left hpow hscale
      _ = 1 := by norm_num [bellmanWeightCap]

theorem normalizedBellmanChargeWeight_mul_inflation
    (mdp : MDP State Action) (stage : Fin mdp.horizon) :
    normalizedBellmanChargeWeight mdp stage * bellmanInflation mdp =
      normalizedBellmanWeight mdp stage := by
  unfold normalizedBellmanChargeWeight normalizedBellmanWeight
  rw [pow_succ']
  ring

theorem normalizedBellmanWeight_mem_Icc
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (stage : Fin mdp.horizon) :
    normalizedBellmanWeight mdp stage ∈ Set.Icc (0 : Real) 1 := by
  have hpow := bellmanInflation_pow_le_cap mdp hhorizon (stage.val + 1)
    (by omega)
  have hpowNonneg : 0 <= bellmanInflation mdp ^ (stage.val + 1) := by
    have : 0 <= bellmanInflation mdp := by
      linarith [bellmanInflation_one_le mdp]
    positivity
  constructor
  · unfold normalizedBellmanWeight
    positivity
  · unfold normalizedBellmanWeight
    have hscale : (0 : Real) <= 31 / 32 := by norm_num
    calc
      (31 / 32 : Real) * bellmanInflation mdp ^ (stage.val + 1) <=
          (31 / 32 : Real) * bellmanWeightCap :=
        mul_le_mul_of_nonneg_left hpow hscale
      _ = 1 := by norm_num [bellmanWeightCap]

/-- The clipped, normalized and chronologically weighted continuation gap used
by the predictable martingale.  Clipping is inactive on the joint confidence
event; normalization keeps the global MGF range exactly `[0,H]`. -/
noncomputable def clippedSuccessorGapFeatureOfSummaries
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) (n : Nat)
    (summaries : Fin (n + 1) -> TransitionCountSummary mdp)
    (stage : Fin mdp.horizon) (state : State) : Real :=
  let previous := recurrentQTableOfSummaries mdp defaultState
    (scale (State := State) (Action := Action) mdp episodes delta) n
    (fun i => summaries i.castSucc)
  let summary := cumulativeSummaryOfSequence summaries
  let remaining := mdp.horizon - (stage.val + 1)
  let raw := clippedPolicyGapRemaining previous summary defaultState
    (scale (State := State) (Action := Action) mdp episodes delta)
    remaining (by omega) state
  normalizedBellmanWeight mdp stage *
    max 0 (min raw (mdp.horizon : Real))

/-- The martingale feature is globally in `[0,H]`, independently of whether
the statistical event holds. -/
theorem clippedSuccessorGapFeatureOfSummaries_mem_Icc
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) (n : Nat)
    (summaries : Fin (n + 1) -> TransitionCountSummary mdp)
    (stage : Fin mdp.horizon) (state : State) :
    clippedSuccessorGapFeatureOfSummaries mdp defaultState episodes delta n
      summaries stage state ∈ Set.Icc (0 : Real) mdp.horizon := by
  have hstage := stage.isLt
  have hhorizon : 0 < mdp.horizon := by omega
  have hweight := normalizedBellmanWeight_mem_Icc mdp hhorizon stage
  have hgap : max 0 (min
      (clippedPolicyGapRemaining
        (recurrentQTableOfSummaries mdp defaultState
          (scale (State := State) (Action := Action) mdp episodes delta) n
          (fun i => summaries i.castSucc))
        (cumulativeSummaryOfSequence summaries) defaultState
        (scale (State := State) (Action := Action) mdp episodes delta)
        (mdp.horizon - (stage.val + 1)) (by omega) state)
      (mdp.horizon : Real)) ∈ Set.Icc (0 : Real) mdp.horizon := by
    exact ⟨le_max_left _ _, max_le (Nat.cast_nonneg _) (min_le_right _ _)⟩
  constructor
  · exact mul_nonneg hweight.1 hgap.1
  · unfold clippedSuccessorGapFeatureOfSummaries
    exact (mul_le_mul hweight.2 hgap.2 hgap.1 (by norm_num)).trans_eq
      (one_mul _)

/-- Compensated batch statistic for one fixed discrete prefix-summary table. -/
noncomputable def successorBellmanStatisticOfSummaries
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) (n : Nat) (tilt : Real)
    (input : (Fin (n + 1) -> TransitionCountSummary mdp) ×
      EpisodeBatch mdp 1) : Real :=
  let summaries := input.1
  let table := recurrentPolicyTableOfSummaries mdp defaultState
    (scale (State := State) (Action := Action) mdp episodes delta)
    (n + 1) summaries
  let feature := clippedSuccessorGapFeatureOfSummaries mdp defaultState
    episodes delta n summaries
  tilt * input.2.cumulativeDeterministicGapInnovation defaultState table feature -
    (mdp.horizon : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8

theorem measurable_successorBellmanStatisticOfSummaries
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) (n : Nat) (tilt : Real) :
    Measurable (successorBellmanStatisticOfSummaries mdp defaultState
      episodes delta n tilt) := by
  letI : MeasurableSingletonClass
      (Fin (n + 1) -> TransitionCountSummary mdp) :=
    Pi.instMeasurableSingletonClass
  apply measurable_prod_of_countable_left
  intro summaries
  let table := recurrentPolicyTableOfSummaries mdp defaultState
    (scale (State := State) (Action := Action) mdp episodes delta)
    (n + 1) summaries
  let feature := clippedSuccessorGapFeatureOfSummaries mdp defaultState
    episodes delta n summaries
  exact (EpisodeBatch.measurable_cumulativeDeterministicGapInnovation
      defaultState table feature |>.const_mul tilt).sub measurable_const

/-- The same statistic with the prefix summarized exactly as the recurrent
planner summarizes it. -/
noncomputable def successorBellmanHistoryBatchStatistic
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) (n : Nat) (tilt : Real)
    (input : EpisodeBatchPrefix mdp 1 n × EpisodeBatch mdp 1) : Real :=
  successorBellmanStatisticOfSummaries mdp defaultState episodes delta n tilt
    (prefixTransitionSummaries input.1, input.2)

theorem measurable_successorBellmanHistoryBatchStatistic
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) (n : Nat) (tilt : Real) :
    Measurable (successorBellmanHistoryBatchStatistic mdp defaultState
      episodes delta n tilt) := by
  exact (measurable_successorBellmanStatisticOfSummaries mdp defaultState
    episodes delta n tilt).comp
      ((measurable_prefixTransitionSummaries.comp measurable_fst).prodMk
        measurable_snd)

namespace AdaptiveEpisodeBatchSource

/-- A successor episode's compensated, prefix-predictable Bellman innovation
has conditional MGF at most one under the literal recurrent batch kernel. -/
theorem recurrentSuccessorBellmanInnovation_compensated_hasCondMGFUpperBoundAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (defaultState : State) (episodes : Nat) (delta : Real)
    (hhorizon : 0 < mdp.horizon) (n : Nat) (tilt : Real) :
    Concentration.HasCondMGFUpperBoundAt
      (BanditRLProof.FiniteHorizonRL.AdaptiveEpisodeBatchSource.batchPrefixFiltration
        (mdp := mdp) 1 n)
      ((BanditRLProof.FiniteHorizonRL.AdaptiveEpisodeBatchSource.batchPrefixFiltration
        (mdp := mdp) 1).le n)
      (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
        successorBellmanHistoryBatchStatistic mdp defaultState episodes delta
          n tilt (Preorder.frestrictLe n trajectory, trajectory (n + 1)))
      1 0
      (recurrentSource mdp initialState defaultState episodes delta
        |>.trajectoryMeasure) := by
  let source := recurrentSource mdp initialState defaultState episodes delta
  let statistic := successorBellmanHistoryBatchStatistic mdp defaultState
    episodes delta n tilt
  have hstatistic : Measurable statistic :=
    measurable_successorBellmanHistoryBatchStatistic mdp defaultState
      episodes delta n tilt
  have hX : Measurable (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
      statistic (Preorder.frestrictLe n trajectory, trajectory (n + 1))) :=
    hstatistic.comp ((Preorder.measurable_frestrictLe n).prodMk
      (measurable_pi_apply (n + 1)))
  let target :=
    ((ProbabilityTheory.Kernel.id ×ₖ source.batchKernel n).map statistic)
  have hmap := source.condExpKernel_map_historyBatchStatistic_eq_batchKernel
    n statistic hstatistic
  have htarget : Filter.Eventually
      (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
        Concentration.HasMGFUpperBoundAt id 1 0
          (target (Preorder.frestrictLe n trajectory)))
      (ae (source.trajectoryMeasure.trim
        ((BanditRLProof.FiniteHorizonRL.AdaptiveEpisodeBatchSource.batchPrefixFiltration
          (mdp := mdp) 1).le n))) := by
    exact Filter.Eventually.of_forall fun trajectory => by
      let history := Preorder.frestrictLe n trajectory
      let summaries := prefixTransitionSummaries history
      let table := recurrentPolicyTableOfSummaries mdp defaultState
        (scale (State := State) (Action := Action) mdp episodes delta)
        (n + 1) summaries
      let feature := clippedSuccessorGapFeatureOfSummaries mdp defaultState
        episodes delta n summaries
      let Zbatch : EpisodeBatch mdp 1 -> Real := fun batch =>
        tilt * batch.cumulativeDeterministicGapInnovation defaultState table feature -
          (mdp.horizon : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8
      have hbatch : Concentration.HasMGFUpperBoundAt Zbatch 1 0
          (source.batchKernel n history) := by
        rw [source.batchKernel_eq_iidEpisodeBatchMeasure n history]
        simpa [Zbatch, table, feature, summaries, source,
          successorBellmanHistoryBatchStatistic,
          successorBellmanStatisticOfSummaries] using
          table.iidEpisodeBatchMeasure_one_cumulativeDeterministicGapInnovation_compensated_hasMGFUpperBoundAt
            initialState defaultState hhorizon feature
            (clippedSuccessorGapFeatureOfSummaries_mem_Icc mdp defaultState
              episodes delta n summaries) tilt
      have hZbatch : Measurable Zbatch :=
        (EpisodeBatch.measurable_cumulativeDeterministicGapInnovation
          defaultState table feature |>.const_mul tilt).sub measurable_const
      change Concentration.HasMGFUpperBoundAt id 1 0 (target history)
      have htargetEq : target history = Measure.map Zbatch
          (source.batchKernel n history) := by
        dsimp [target]
        rw [ProbabilityTheory.Kernel.map_apply _ hstatistic]
        rw [ProbabilityTheory.Kernel.prod_apply,
          ProbabilityTheory.Kernel.id_apply, Measure.dirac_prod]
        rw [Measure.map_map hstatistic measurable_prodMk_left]
        rfl
      rw [htargetEq]
      exact (Concentration.HasMGFUpperBoundAt.id_map_iff
        hZbatch.aemeasurable).2 hbatch
  have hintegrable : forall s, Integrable
      (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
        Real.exp (s * statistic
          (Preorder.frestrictLe n trajectory, trajectory (n + 1))))
      source.trajectoryMeasure := by
    intro s
    let bound := |tilt| * (mdp.horizon : Real) ^ 2 +
      |(mdp.horizon : Real) * tilt ^ 2 * (mdp.horizon : Real) ^ 2 / 8|
    apply Integrable.of_bound
      ((Real.measurable_exp.comp (hX.const_mul s)).aestronglyMeasurable)
      (Real.exp (|s| * bound))
    exact Filter.Eventually.of_forall fun trajectory => by
      let history := Preorder.frestrictLe n trajectory
      let summaries := prefixTransitionSummaries history
      let table := recurrentPolicyTableOfSummaries mdp defaultState
        (scale (State := State) (Action := Action) mdp episodes delta)
        (n + 1) summaries
      let feature := clippedSuccessorGapFeatureOfSummaries mdp defaultState
        episodes delta n summaries
      have hinnovation := mdp.abs_sampledCumulativeDeterministicGapInnovationFrom_le
        table feature
        (clippedSuccessorGapFeatureOfSummaries_mem_Icc mdp defaultState
          episodes delta n summaries)
        mdp.horizon le_rfl
        ((trajectory (n + 1)).reconstructedInitialState defaultState)
        ((trajectory (n + 1)).reconstructedStepTrace)
      have hstatBound :
          |statistic (history, trajectory (n + 1))| <= bound := by
        dsimp [statistic, successorBellmanHistoryBatchStatistic,
          successorBellmanStatisticOfSummaries, summaries, table, feature,
          EpisodeBatch.cumulativeDeterministicGapInnovation]
        calc
          |_ - _| <= |tilt *
              mdp.sampledCumulativeDeterministicGapInnovationFrom table feature
                mdp.horizon le_rfl
                ((trajectory (n + 1)).reconstructedInitialState defaultState)
                ((trajectory (n + 1)).reconstructedStepTrace)| +
              |(mdp.horizon : Real) * tilt ^ 2 *
                (mdp.horizon : Real) ^ 2 / 8| := abs_sub _ _
          _ <= bound := by
            rw [abs_mul]
            exact add_le_add
              (mul_le_mul_of_nonneg_left (by simpa only [pow_two] using hinnovation)
                (abs_nonneg tilt)) le_rfl
      change |Real.exp (s * statistic (history, trajectory (n + 1)))| <= _
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        s * statistic (history, trajectory (n + 1)) <=
            |s| * |statistic (history, trajectory (n + 1))| :=
          (le_abs_self _).trans_eq (abs_mul _ _)
        _ <= |s| * bound :=
          mul_le_mul_of_nonneg_left hstatBound (abs_nonneg s)
  have hcond :=
    BanditRLProof.FiniteHorizonRL.AdaptiveEpisodeBatchSource.hasCondMGFUpperBoundAt_of_condExpKernel_map_eq
    source.trajectoryMeasure
    (BanditRLProof.FiniteHorizonRL.AdaptiveEpisodeBatchSource.batchPrefixFiltration
      (mdp := mdp) 1 n)
    ((BanditRLProof.FiniteHorizonRL.AdaptiveEpisodeBatchSource.batchPrefixFiltration
      (mdp := mdp) 1).le n)
    (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
      statistic (Preorder.frestrictLe n trajectory, trajectory (n + 1)))
    hX 1 0
    (fun trajectory => target (Preorder.frestrictLe n trajectory))
    hintegrable (by
      simpa [BanditRLProof.FiniteHorizonRL.AdaptiveEpisodeBatchSource.batchPrefixFiltration,
        source] using hmap) htarget
  simpa [source, statistic] using hcond

end AdaptiveEpisodeBatchSource

/-- The un-compensated Bellman innovation of one successor episode, with the
policy and clipped gap feature read from one fixed prefix-summary table. -/
noncomputable def successorBellmanInnovationOfSummaries
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) (n : Nat)
    (input : (Fin (n + 1) -> TransitionCountSummary mdp) ×
      EpisodeBatch mdp 1) : Real :=
  let summaries := input.1
  let table := recurrentPolicyTableOfSummaries mdp defaultState
    (scale (State := State) (Action := Action) mdp episodes delta)
    (n + 1) summaries
  let feature := clippedSuccessorGapFeatureOfSummaries mdp defaultState
    episodes delta n summaries
  input.2.cumulativeDeterministicGapInnovation defaultState table feature

theorem measurable_successorBellmanInnovationOfSummaries
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) (n : Nat) :
    Measurable (successorBellmanInnovationOfSummaries mdp defaultState
      episodes delta n) := by
  letI : MeasurableSingletonClass
      (Fin (n + 1) -> TransitionCountSummary mdp) :=
    Pi.instMeasurableSingletonClass
  apply measurable_prod_of_countable_left
  intro summaries
  let table := recurrentPolicyTableOfSummaries mdp defaultState
    (scale (State := State) (Action := Action) mdp episodes delta)
    (n + 1) summaries
  let feature := clippedSuccessorGapFeatureOfSummaries mdp defaultState
    episodes delta n summaries
  exact EpisodeBatch.measurable_cumulativeDeterministicGapInnovation
    defaultState table feature

/-- The successor Bellman innovation with the recurrent prefix summarized in
exactly the same way as the generated source. -/
noncomputable def successorBellmanInnovationOfHistoryBatch
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) (n : Nat)
    (input : EpisodeBatchPrefix mdp 1 n × EpisodeBatch mdp 1) : Real :=
  successorBellmanInnovationOfSummaries mdp defaultState episodes delta n
    (prefixTransitionSummaries input.1, input.2)

theorem measurable_successorBellmanInnovationOfHistoryBatch
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) (n : Nat) :
    Measurable (successorBellmanInnovationOfHistoryBatch mdp defaultState
      episodes delta n) := by
  exact (measurable_successorBellmanInnovationOfSummaries mdp defaultState
    episodes delta n).comp
      ((measurable_prefixTransitionSummaries.comp measurable_fst).prodMk
        measurable_snd)

/-- Prefix-predictable Bellman innovation.  Coordinate zero is deliberately
zero: the canonical initial episode is charged separately by its deterministic
`H` envelope, while every successor coordinate uses its strict prefix. -/
noncomputable def recurrentBellmanInnovationPrefix
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) :
    (round : Nat) -> EpisodeBatchPrefix mdp 1 round -> Real
  | 0, _history => 0
  | n + 1, history =>
      successorBellmanInnovationOfHistoryBatch mdp defaultState episodes delta n
        (Preorder.frestrictLe₂
          (π := fun _ : Nat => EpisodeBatch mdp 1)
          (Nat.le_succ n) history,
          history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

theorem measurable_recurrentBellmanInnovationPrefix
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) (round : Nat) :
    Measurable (recurrentBellmanInnovationPrefix mdp defaultState
      episodes delta round) := by
  cases round with
  | zero =>
      change Measurable (fun _ : EpisodeBatchPrefix mdp 1 0 => (0 : Real))
      exact measurable_const
  | succ n =>
      simpa [recurrentBellmanInnovationPrefix] using
        (measurable_successorBellmanInnovationOfHistoryBatch mdp defaultState
          episodes delta n).comp
          ((Preorder.measurable_frestrictLe₂
              (X := fun _ : Nat => EpisodeBatch mdp 1) (Nat.le_succ n)).prodMk
            (measurable_pi_apply
              (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1))))

/-- Actual successor-episode Bellman innovation process on the generated
recurrent trajectory. -/
noncomputable def recurrentBellmanInnovationProcess
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) (round : Nat)
    (trajectory : EpisodeBatchTrajectory mdp 1) : Real :=
  recurrentBellmanInnovationPrefix mdp defaultState episodes delta round
    (Preorder.frestrictLe round trajectory)

/-- Deterministic per-episode variance budget.  Coordinate zero is zero because
its regret is paid separately; every successor episode has budget `H^3`. -/
noncomputable def recurrentBellmanInnovationVarianceProcess
    (mdp : MDP State Action) (round : Nat)
    (_trajectory : EpisodeBatchTrajectory mdp 1) : Real :=
  match round with
  | 0 => 0
  | _ + 1 => (mdp.horizon : Real) * (mdp.horizon : Real) ^ 2

theorem recurrentBellmanInnovation_compensated_stronglyAdapted
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta tilt : Real) :
    StronglyAdapted
      (BanditRLProof.FiniteHorizonRL.AdaptiveEpisodeBatchSource.batchPrefixFiltration
        (mdp := mdp) 1)
      (fun round trajectory =>
        tilt * recurrentBellmanInnovationProcess mdp defaultState episodes delta
            round trajectory -
          (tilt ^ 2 / 8) *
            recurrentBellmanInnovationVarianceProcess mdp round trajectory) := by
  intro round
  cases round with
  | zero =>
      have hprefix : Measurable
          (fun _history : EpisodeBatchPrefix mdp 1 0 => (0 : Real)) :=
        measurable_const
      simpa [recurrentBellmanInnovationProcess,
        recurrentBellmanInnovationPrefix,
        recurrentBellmanInnovationVarianceProcess] using
        (hprefix.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  | succ n =>
      have hprefix : Measurable
          (fun history : EpisodeBatchPrefix mdp 1 (n + 1) =>
            tilt * recurrentBellmanInnovationPrefix mdp defaultState episodes
                delta (n + 1) history -
              (tilt ^ 2 / 8) *
                ((mdp.horizon : Real) * (mdp.horizon : Real) ^ 2)) :=
        ((measurable_recurrentBellmanInnovationPrefix mdp defaultState episodes
          delta (n + 1)).const_mul tilt).sub measurable_const
      simpa [recurrentBellmanInnovationProcess,
        recurrentBellmanInnovationVarianceProcess] using
        (hprefix.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable

/-- Coordinate zero has the trivial compensated MGF certificate. -/
theorem recurrentBellmanInnovation_zero_compensated_hasMGFUpperBoundAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (defaultState : State) (episodes : Nat) (delta tilt : Real) :
    Concentration.HasMGFUpperBoundAt
      (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
        tilt * recurrentBellmanInnovationProcess mdp defaultState episodes delta
            0 trajectory -
          (tilt ^ 2 / 8) *
            recurrentBellmanInnovationVarianceProcess mdp 0 trajectory)
      1 0
      (recurrentSource mdp initialState defaultState episodes delta
        |>.trajectoryMeasure) := by
  constructor
  · intro s
    simp [recurrentBellmanInnovationProcess,
      recurrentBellmanInnovationPrefix,
      recurrentBellmanInnovationVarianceProcess]
  · simp [ProbabilityTheory.mgf, recurrentBellmanInnovationProcess,
      recurrentBellmanInnovationPrefix,
      recurrentBellmanInnovationVarianceProcess]

/-- Fixed-tilt upper tail for the sum of the generated successor-episode
Bellman innovations.  The source, prefix policy, and transition law are the
same objects as in the recurrent planner. -/
theorem trajectoryMeasure_recurrentBellmanInnovation_sum_ge_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (defaultState : State) (episodes : Nat) (delta : Real)
    (hhorizon : 0 < mdp.horizon)
    (tilt threshold : Real) (htilt : 0 < tilt) :
    let source := recurrentSource mdp initialState defaultState episodes delta
    source.trajectoryMeasure
        {trajectory |
          threshold <= (Finset.range episodes).sum (fun round =>
            recurrentBellmanInnovationProcess mdp defaultState episodes delta
              round trajectory)} <=
      ENNReal.ofReal (Real.exp
        (-tilt * threshold + (tilt ^ 2 / 8) *
          ((episodes : Real) *
            ((mdp.horizon : Real) * (mdp.horizon : Real) ^ 2)))) := by
  dsimp only
  let source := recurrentSource mdp initialState defaultState episodes delta
  let F :=
    BanditRLProof.FiniteHorizonRL.AdaptiveEpisodeBatchSource.batchPrefixFiltration
      (mdp := mdp) 1
  let Y : Nat -> EpisodeBatchTrajectory mdp 1 -> Real :=
    recurrentBellmanInnovationProcess mdp defaultState episodes delta
  let V : Nat -> EpisodeBatchTrajectory mdp 1 -> Real :=
    recurrentBellmanInnovationVarianceProcess mdp
  let varianceCoeff := tilt ^ 2 / 8
  let varianceBudget := (episodes : Real) *
    ((mdp.horizon : Real) * (mdp.horizon : Real) ^ 2)
  have hadapted : StronglyAdapted F (fun round trajectory =>
      tilt * Y round trajectory - varianceCoeff * V round trajectory) := by
    simpa [F, Y, V, varianceCoeff] using
      recurrentBellmanInnovation_compensated_stronglyAdapted mdp defaultState
        episodes delta tilt
  have hzero : Concentration.HasMGFUpperBoundAt
      (fun trajectory => tilt * Y 0 trajectory - varianceCoeff * V 0 trajectory)
      1 0 source.trajectoryMeasure := by
    simpa [source, Y, V, varianceCoeff] using
      recurrentBellmanInnovation_zero_compensated_hasMGFUpperBoundAt
        (mdp := mdp) (initialState := initialState)
        defaultState episodes delta tilt
  have hsucc : ∀ i, i < episodes - 1 ->
      Concentration.HasCondMGFUpperBoundAt
        (F i) (F.le i)
        (fun trajectory =>
          tilt * Y (i + 1) trajectory - varianceCoeff * V (i + 1) trajectory)
        1 0 source.trajectoryMeasure := by
    intro i _hi
    have h :=
      AdaptiveCumulativeHoeffdingUCBVI.AdaptiveEpisodeBatchSource.recurrentSuccessorBellmanInnovation_compensated_hasCondMGFUpperBoundAt
        (mdp := mdp) (initialState := initialState) defaultState episodes delta
        hhorizon i tilt
    have hrestrict (trajectory : EpisodeBatchTrajectory mdp 1) :
        Preorder.frestrictLe₂
            (π := fun _ : Nat => EpisodeBatch mdp 1) (Nat.le_succ i)
            (Preorder.frestrictLe (i + 1) trajectory) =
          Preorder.frestrictLe i trajectory := rfl
    have hfun :
        (fun trajectory =>
          tilt * Y (i + 1) trajectory - varianceCoeff * V (i + 1) trajectory) =
        (fun trajectory =>
          successorBellmanHistoryBatchStatistic mdp defaultState episodes delta
            i tilt (Preorder.frestrictLe i trajectory, trajectory (i + 1))) := by
      funext trajectory
      simp [Y, V, varianceCoeff, recurrentBellmanInnovationProcess,
        recurrentBellmanInnovationPrefix,
        recurrentBellmanInnovationVarianceProcess, hrestrict,
        successorBellmanInnovationOfHistoryBatch,
        successorBellmanInnovationOfSummaries,
        successorBellmanHistoryBatchStatistic,
        successorBellmanStatisticOfSummaries]
      ring
    rw [hfun]
    simpa [F, source] using h
  have hvarianceCoeff : 0 <= varianceCoeff := by
    dsimp [varianceCoeff]
    positivity
  have htail :=
    Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
      Y V episodes tilt varianceCoeff threshold varianceBudget
      hadapted hzero hsucc htilt.le hvarianceCoeff
  have hbudget : ∀ trajectory,
      (Finset.range episodes).sum (fun round => V round trajectory) <=
        varianceBudget := by
    intro trajectory
    calc
      (Finset.range episodes).sum (fun round => V round trajectory) <=
          (Finset.range episodes).sum (fun _round =>
            (mdp.horizon : Real) * (mdp.horizon : Real) ^ 2) := by
        apply Finset.sum_le_sum
        intro round _hround
        cases round with
        | zero =>
            simp [V, recurrentBellmanInnovationVarianceProcess]
            positivity
        | succ n =>
            simp [V, recurrentBellmanInnovationVarianceProcess]
      _ = varianceBudget := by simp [varianceBudget]
  calc
    source.trajectoryMeasure
        {trajectory | threshold <= (Finset.range episodes).sum (fun round =>
          Y round trajectory)} <=
      source.trajectoryMeasure
        {trajectory |
          threshold <= (Finset.range episodes).sum (fun round =>
            Y round trajectory) ∧
          (Finset.range episodes).sum (fun round => V round trajectory) <=
            varianceBudget} := by
        apply measure_mono
        intro trajectory htrajectory
        exact ⟨htrajectory, hbudget trajectory⟩
    _ <= ENNReal.ofReal (Real.exp
        (-tilt * threshold + varianceCoeff * varianceBudget)) := htail
    _ = ENNReal.ofReal (Real.exp
        (-tilt * threshold + (tilt ^ 2 / 8) *
          ((episodes : Real) *
            ((mdp.horizon : Real) * (mdp.horizon : Real) ^ 2)))) := by
      rfl

end AdaptiveCumulativeHoeffdingUCBVI

end BanditRLProof.FiniteHorizonRL
