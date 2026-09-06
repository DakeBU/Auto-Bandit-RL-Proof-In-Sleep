import BanditRLProof.Exp3RealizedConcentration

/-!
# Finite-horizon realized EXP3 concentration

This module shifts the generated predictable realized-deviation process by one
time step so that its deterministic zero initial value and every actual round
fit Mathlib's conditional sub-Gaussian sum theorem.  The resulting public
theorem bounds the full finite-horizon realized-minus-exploration-mixed loss
sum under a probability environment prior.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

theorem sampledPredictableSelectedDeviation_zero_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) -> Action × Real) => sample.1))
      measurable_fst.comap_le
      (sampledTrajectorySelectedDeviationAt arms eta gamma loss 0)
      (Concentration.intervalVarianceProxy 0 1) mu := by
  dsimp only
  let algorithm := sampledImportanceWeightedHistoryAlgorithm arms harms
    eta gamma hgamma_nonneg hgamma_le_one
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
  have hhistory : Measurable history := measurable_fst
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.2 0).1
  let prob := fun _env : Env => initialExploredDistribution arms eta gamma
  let roundLoss := loss.initial
  let mean := fun env : Env =>
    arms.sum (fun selected => prob env selected * roundLoss env selected)
  let source := sampledInitialEnvironmentDistributionSource
    (Env := Env) arms harms eta gamma hgamma_nonneg hgamma_le_one
  let mcond := (inferInstance : MeasurableSpace Env).comap history
  letI : MeasurableSpace (Env × ((k : Nat) -> Action × Real)) :=
    Prod.instMeasurableSpace
  let X := sampledTrajectorySelectedDeviationAt arms eta gamma loss 0
  let target : (Env × ((k : Nat) -> Action × Real)) -> Measure Real :=
    fun omega => Measure.map
      (fun selected => roundLoss (history omega) selected - mean (history omega))
      (finiteActionMeasure arms (prob (history omega)))
  have haction : Measurable action := by fun_prop
  have hmcond : mcond <= Prod.instMeasurableSpace := hhistory.comap_le
  have hX : Measurable X := by
    simpa [X] using
      (measurable_sampledTrajectorySelectedDeviationAt
        arms harms eta gamma hgamma_nonneg hgamma_le_one loss 0)
  have hkernel : Kernel.const Env algorithm.initialAction =
      finiteActionKernel arms prob source := by
    ext env event hevent
    rw [Kernel.const_apply, finiteActionKernel_apply]
    rfl
  have hcond : condDistrib action history mu =ᵐ[mu.map history]
      finiteActionKernel arms prob source := by
    have hbase :=
      canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action_zero_given_environment
        prior algorithm loss.environment
    rw [hkernel] at hbase
    simpa [mu, algorithm, history, action,
      sampledImportanceWeightedTrajectoryKernel] using hbase
  have haction_map :=
    condExpKernel_map_eq_finiteActionMeasure_of_condDistrib_ae_eq
      mu action history haction hhistory arms prob source hcond
  have hhistory_mcond :
      @Measurable (Env × ((k : Nat) -> Action × Real)) Env
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
      exact (loss.measurable_initial.comp
        (measurable_const.prodMk measurable_id)).sub measurable_const
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
    have hraw : Measurable raw :=
      loss.measurable_initial.comp (measurable_const.prodMk measurable_id)
    have hbound : Filter.Eventually
        (fun selected => raw selected ∈ Set.Icc (0 : Real) 1) (ae actionMu) :=
      Filter.Eventually.of_forall fun selected =>
        loss.initial_mem_unitInterval (history omega) selected
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

theorem sampledPredictableRealizedDeviation_zero_hasCondSubgaussianMGF
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    ProbabilityTheory.HasCondSubgaussianMGF
      ((inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) -> Action × Real) => sample.1))
      measurable_fst.comap_le
      (sampledTrajectoryRealizedDeviationAt arms eta gamma loss 0)
      (Concentration.intervalVarianceProxy 0 1) mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
  have hhistory : Measurable history := measurable_fst
  let mcond := (inferInstance : MeasurableSpace Env).comap history
  letI : MeasurableSpace (Env × ((k : Nat) -> Action × Real)) :=
    Prod.instMeasurableSpace
  have hmcond : mcond <= Prod.instMeasurableSpace := hhistory.comap_le
  have hselected :=
    sampledPredictableSelectedDeviation_zero_hasCondSubgaussianMGF
      prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss
  dsimp only at hselected
  have hreward :=
    sampledTrajectoryRealizedLossAt_ae_eq_selectedPredictable
      prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss 0
  dsimp only at hreward
  have hdeviation :
      sampledTrajectorySelectedDeviationAt arms eta gamma loss 0 =ᵐ[mu]
        sampledTrajectoryRealizedDeviationAt arms eta gamma loss 0 := by
    filter_upwards [hreward] with sample hs
    simp only [sampledTrajectorySelectedDeviationAt,
      sampledTrajectoryRealizedDeviationAt]
    rw [hs]
  change ProbabilityTheory.Kernel.HasSubgaussianMGF
    (sampledTrajectorySelectedDeviationAt arms eta gamma loss 0)
    (Concentration.intervalVarianceProxy 0 1)
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond) at hselected
  change ProbabilityTheory.Kernel.HasSubgaussianMGF
    (sampledTrajectoryRealizedDeviationAt arms eta gamma loss 0)
    (Concentration.intervalVarianceProxy 0 1)
    (@condExpKernel (Env × ((k : Nat) -> Action × Real)) inferInstance _
      mu _ mcond) (mu.trim hmcond)
  apply (ProbabilityTheory.Kernel.HasSubgaussianMGF_congr ?_).1 hselected
  rw [@ProbabilityTheory.condExpKernel_comp_trim
    (Env × ((k : Nat) -> Action × Real)) mcond inferInstance _ mu _ hmcond]
  exact hdeviation

def sampledPredictableDeviationFiltration
    (Env : Type u) (Action : Type v)
    [MeasurableSpace Env] [MeasurableSpace Action] :
    Filtration Nat (inferInstance : MeasurableSpace
      (Env × ((k : Nat) -> Action × Real))) where
  seq
    | 0 => (inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) -> Action × Real) => sample.1)
    | i + 1 => (inferInstance : MeasurableSpace
        (Env × History.FinitePairHistory Action Real i)).comap
          (fun sample : Env × ((k : Nat) -> Action × Real) =>
            (sample.1, Preorder.frestrictLe i sample.2))
  mono' := by
    intro i j hij
    cases i with
    | zero =>
        cases j with
        | zero => exact le_rfl
        | succ j =>
            let historyJ := fun sample : Env × ((k : Nat) -> Action × Real) =>
              (sample.1, Preorder.frestrictLe j sample.2)
            have hhistoryJ :
                @Measurable (Env × ((k : Nat) -> Action × Real))
                  (Env × History.FinitePairHistory Action Real j)
                  ((inferInstance : MeasurableSpace
                    (Env × History.FinitePairHistory Action Real j)).comap historyJ)
                  inferInstance historyJ := Measurable.of_comap_le le_rfl
            have hfst :
                @Measurable (Env × ((k : Nat) -> Action × Real)) Env
                  ((inferInstance : MeasurableSpace
                    (Env × History.FinitePairHistory Action Real j)).comap historyJ)
                  inferInstance Prod.fst :=
              (measurable_fst : Measurable
                (fun input : Env × History.FinitePairHistory Action Real j =>
                  input.1)).comp hhistoryJ
            exact hfst.comap_le
    | succ i =>
        cases j with
        | zero => exact (Nat.not_succ_le_zero i hij).elim
        | succ j =>
            have hij' : i <= j := Nat.succ_le_succ_iff.mp hij
            let historyI := fun sample : Env × ((k : Nat) -> Action × Real) =>
              (sample.1, Preorder.frestrictLe i sample.2)
            let historyJ := fun sample : Env × ((k : Nat) -> Action × Real) =>
              (sample.1, Preorder.frestrictLe j sample.2)
            let restrictHistory :
                (Env × History.FinitePairHistory Action Real j) ->
                  (Env × History.FinitePairHistory Action Real i) :=
              fun input => (input.1,
                Preorder.frestrictLe₂ (π := fun _ : Nat => Action × Real) hij' input.2)
            have hrestrict : Measurable restrictHistory :=
              measurable_fst.prodMk
                ((Preorder.measurable_frestrictLe₂ hij').comp measurable_snd)
            have hhistoryJ :
                @Measurable (Env × ((k : Nat) -> Action × Real))
                  (Env × History.FinitePairHistory Action Real j)
                  ((inferInstance : MeasurableSpace
                    (Env × History.FinitePairHistory Action Real j)).comap historyJ)
                  inferInstance historyJ := Measurable.of_comap_le le_rfl
            have hhistoryI :
                @Measurable (Env × ((k : Nat) -> Action × Real))
                  (Env × History.FinitePairHistory Action Real i)
                  ((inferInstance : MeasurableSpace
                    (Env × History.FinitePairHistory Action Real j)).comap historyJ)
                  inferInstance historyI := by
              have hcomp := hrestrict.comp hhistoryJ
              convert hcomp using 1
            exact hhistoryI.comap_le
  le' := by
    intro i
    cases i with
    | zero => exact measurable_fst.comap_le
    | succ i =>
        exact (measurable_fst.prodMk
          ((Preorder.measurable_frestrictLe i).comp measurable_snd)).comap_le

@[simp]
theorem sampledPredictableDeviationFiltration_zero
    (Env : Type u) (Action : Type v)
    [MeasurableSpace Env] [MeasurableSpace Action] :
    sampledPredictableDeviationFiltration Env Action 0 =
      (inferInstance : MeasurableSpace Env).comap
        (fun sample : Env × ((k : Nat) -> Action × Real) => sample.1) := rfl

@[simp]
theorem sampledPredictableDeviationFiltration_succ
    (Env : Type u) (Action : Type v)
    [MeasurableSpace Env] [MeasurableSpace Action] (i : Nat) :
    sampledPredictableDeviationFiltration Env Action (i + 1) =
      (inferInstance : MeasurableSpace
        (Env × History.FinitePairHistory Action Real i)).comap
          (fun sample : Env × ((k : Nat) -> Action × Real) =>
            (sample.1, Preorder.frestrictLe i sample.2)) := rfl

noncomputable def sampledPredictableRealizedDeviationProcess
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) :
    Nat -> Env × ((k : Nat) -> Action × Real) -> Real
  | 0, _sample => 0
  | i + 1, sample =>
      sampledTrajectoryRealizedDeviationAt arms eta gamma loss i sample

noncomputable def sampledPredictableRealizedDeviationProxy : Nat -> NNReal
  | 0 => 0
  | _i + 1 => Concentration.intervalVarianceProxy 0 1

theorem sampledPredictableRealizedDeviationProcess_stronglyAdapted
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) :
    StronglyAdapted
      (sampledPredictableDeviationFiltration Env Action)
      (sampledPredictableRealizedDeviationProcess
        arms eta gamma loss) := by
  intro t
  cases t with
  | zero =>
      simpa [sampledPredictableRealizedDeviationProcess] using
        (stronglyMeasurable_const :
          StronglyMeasurable[
            sampledPredictableDeviationFiltration Env Action 0]
              (fun _ : Env × ((k : Nat) -> Action × Real) => (0 : Real)))
  | succ i =>
      cases i with
      | zero =>
          let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
            (sample.1, Preorder.frestrictLe 0 sample.2)
          let selectedReward := fun input :
              Env × History.FinitePairHistory Action Real 0 =>
            (input.2 ⟨0, by simp⟩).2
          let mean := fun input :
              Env × History.FinitePairHistory Action Real 0 =>
            arms.sum (fun selected =>
              initialExploredDistribution arms eta gamma selected *
                loss.initial input.1 selected)
          let score := fun input :
              Env × History.FinitePairHistory Action Real 0 =>
            selectedReward input - mean input
          have hhistory :
              @Measurable (Env × ((k : Nat) -> Action × Real))
                (Env × History.FinitePairHistory Action Real 0)
                (sampledPredictableDeviationFiltration Env Action 1)
                inferInstance history := by
            rw [sampledPredictableDeviationFiltration_succ]
            exact Measurable.of_comap_le le_rfl
          have hcoordinate : Measurable
              (fun h : History.FinitePairHistory Action Real 0 =>
                h (⟨0, by simp⟩ : ↑(Finset.Iic 0))) :=
            measurable_pi_apply (⟨0, by simp⟩ : ↑(Finset.Iic 0))
          have hselectedReward : Measurable selectedReward := by
            exact measurable_snd.comp (hcoordinate.comp measurable_snd)
          have hmean : Measurable mean := by
            refine Finset.measurable_sum arms fun selected _hselected => ?_
            exact measurable_const.mul
              (loss.measurable_initial.comp
                (measurable_fst.prodMk measurable_const))
          have hscore : Measurable score := hselectedReward.sub hmean
          have hfactor :
              sampledPredictableRealizedDeviationProcess
                  arms eta gamma loss 1 = score ∘ history := by
            funext sample
            simp [sampledPredictableRealizedDeviationProcess, score,
              selectedReward, mean, history,
              sampledTrajectoryRealizedDeviationAt,
              sampledTrajectoryRealizedLossAt,
              sampledTrajectoryExploredPredictableLossAt,
              sampledTrajectoryProbabilityAt, predictableLossAt]
          rw [hfactor]
          exact (hscore.comp hhistory).stronglyMeasurable
      | succ n =>
          let history := fun sample : Env × ((k : Nat) -> Action × Real) =>
            (sample.1, Preorder.frestrictLe (n + 1) sample.2)
          let previous := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            (input.1,
              Preorder.frestrictLe₂
                (π := fun _ : Nat => Action × Real) n.le_succ input.2)
          let selectedReward := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            (input.2 ⟨n + 1, by simp⟩).2
          let mean := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            arms.sum (fun selected =>
              sampledHistoryDistribution arms eta gamma n (previous input).2 selected *
                loss.successor n (previous input).1 (previous input).2 selected)
          let score := fun input :
              Env × History.FinitePairHistory Action Real (n + 1) =>
            selectedReward input - mean input
          have hhistory :
              @Measurable (Env × ((k : Nat) -> Action × Real))
                (Env × History.FinitePairHistory Action Real (n + 1))
                (sampledPredictableDeviationFiltration Env Action (n + 2))
                inferInstance history := by
            rw [show n + 2 = (n + 1) + 1 by omega,
              sampledPredictableDeviationFiltration_succ]
            exact Measurable.of_comap_le le_rfl
          have hprevious : Measurable previous :=
            measurable_fst.prodMk
              ((Preorder.measurable_frestrictLe₂ n.le_succ).comp measurable_snd)
          have hcoordinate : Measurable
              (fun h : History.FinitePairHistory Action Real (n + 1) =>
                h (⟨n + 1, by simp⟩ : ↑(Finset.Iic (n + 1)))) :=
            measurable_pi_apply
              (⟨n + 1, by simp⟩ : ↑(Finset.Iic (n + 1)))
          have hselectedReward : Measurable selectedReward := by
            exact measurable_snd.comp (hcoordinate.comp measurable_snd)
          let source := sampledEnvironmentHistoryDistributionSource
            (Env := Env) arms harms eta gamma hgamma_nonneg hgamma_le_one n
          have hmean : Measurable mean := by
            refine Finset.measurable_sum arms fun selected hselected => ?_
            exact
                ((source.measurable_prob selected hselected).comp hprevious).mul
                  ((loss.measurable_successor n).comp
                    ((measurable_fst.comp hprevious).prodMk
                      ((measurable_snd.comp hprevious).prodMk measurable_const)))
          have hscore : Measurable score := hselectedReward.sub hmean
          have hfactor :
              sampledPredictableRealizedDeviationProcess
                  arms eta gamma loss (n + 2) = score ∘ history := by
            funext sample
            have hprefix :
                Preorder.frestrictLe₂
                    (π := fun _ : Nat => Action × Real) n.le_succ
                    (Preorder.frestrictLe (n + 1) sample.2) =
                  Preorder.frestrictLe n sample.2 := by
              rfl
            simp [sampledPredictableRealizedDeviationProcess, score,
              selectedReward, mean, previous, history,
              sampledTrajectoryRealizedDeviationAt,
              sampledTrajectoryRealizedLossAt,
              sampledTrajectoryExploredPredictableLossAt,
              sampledTrajectoryProbabilityAt, predictableLossAt, hprefix]
          rw [hfactor]
          exact (hscore.comp hhistory).stronglyMeasurable

theorem sampledPredictableRealizedDeviationProcess_sum_range_succ
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    (Finset.range (horizon + 1)).sum (fun i =>
        sampledPredictableRealizedDeviationProcess
          arms eta gamma loss i sample) =
      (Finset.range horizon).sum (fun i =>
        sampledTrajectoryRealizedDeviationAt arms eta gamma loss i sample) := by
  induction horizon with
  | zero =>
      simp [sampledPredictableRealizedDeviationProcess]
  | succ n ih =>
      calc
        (Finset.range (Nat.succ n + 1)).sum (fun i =>
            sampledPredictableRealizedDeviationProcess
              arms eta gamma loss i sample) =
            (Finset.range (n + 1)).sum (fun i =>
              sampledPredictableRealizedDeviationProcess
                arms eta gamma loss i sample) +
              sampledPredictableRealizedDeviationProcess
                arms eta gamma loss (n + 1) sample := by
                  rw [Finset.sum_range_succ]
        _ = (Finset.range n).sum (fun i =>
              sampledTrajectoryRealizedDeviationAt
                arms eta gamma loss i sample) +
              sampledTrajectoryRealizedDeviationAt
                arms eta gamma loss n sample := by
                  rw [ih]
                  rfl
        _ = (Finset.range (Nat.succ n)).sum (fun i =>
              sampledTrajectoryRealizedDeviationAt
                arms eta gamma loss i sample) := by
                  rw [Finset.sum_range_succ]

theorem sampledPredictableRealizedDeviationProxy_sum_range_succ
    (horizon : Nat) :
    (Finset.range (horizon + 1)).sum
        sampledPredictableRealizedDeviationProxy =
      (horizon : NNReal) * Concentration.intervalVarianceProxy 0 1 := by
  induction horizon with
  | zero =>
      simp [sampledPredictableRealizedDeviationProxy]
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by rfl,
        Finset.sum_range_succ, ih]
      simp only [sampledPredictableRealizedDeviationProxy]
      push_cast
      ring

/-- Finite-horizon one-sided concentration for the realized predictable EXP3
deviation from its exploration-mixed conditional mean. -/
theorem sampledPredictableRealizedDeviation_sum_tail_ennreal
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    {eps : Real} (heps : 0 <= eps) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    mu {sample | eps <= (Finset.range horizon).sum (fun i =>
        sampledTrajectoryRealizedDeviationAt arms eta gamma loss i sample)} <=
      ENNReal.ofReal (Real.exp
        (-eps ^ 2 /
          (2 * ((((horizon : NNReal) *
            Concentration.intervalVarianceProxy 0 1 : NNReal)) : Real)))) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  let F := sampledPredictableDeviationFiltration Env Action
  let Y := sampledPredictableRealizedDeviationProcess
    arms eta gamma loss
  let cY := sampledPredictableRealizedDeviationProxy
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hadapted : StronglyAdapted F Y := by
    simpa [F, Y] using
      (sampledPredictableRealizedDeviationProcess_stronglyAdapted
        arms harms eta gamma hgamma_nonneg hgamma_le_one loss)
  have hzero : ProbabilityTheory.HasSubgaussianMGF
      (Y 0) (cY 0) mu := by
    change ProbabilityTheory.HasSubgaussianMGF (fun _ => 0) 0 mu
    exact ProbabilityTheory.HasSubgaussianMGF.fun_zero
  have hcond : forall i, i < (horizon + 1) - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu := by
    intro i _hi
    cases i with
    | zero =>
        simpa [mu, F, Y, cY,
          sampledPredictableRealizedDeviationProcess,
          sampledPredictableRealizedDeviationProxy] using
          (sampledPredictableRealizedDeviation_zero_hasCondSubgaussianMGF
            prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss)
    | succ n =>
        simpa [mu, F, Y, cY,
          sampledPredictableRealizedDeviationProcess,
          sampledPredictableRealizedDeviationProxy,
          Nat.succ_eq_add_one, Nat.add_assoc] using
          (sampledPredictableRealizedDeviation_succ_hasCondSubgaussianMGF
            prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss n)
  have htail := Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted
    hadapted hzero (horizon + 1) hcond heps
  have hprocess (sample : Env × ((k : Nat) -> Action × Real)) :=
    sampledPredictableRealizedDeviationProcess_sum_range_succ
      arms eta gamma loss horizon sample
  have hproxy :=
    sampledPredictableRealizedDeviationProxy_sum_range_succ horizon
  simpa [Y, cY, hprocess, hproxy] using htail

end BanditRLProof.Exp3
