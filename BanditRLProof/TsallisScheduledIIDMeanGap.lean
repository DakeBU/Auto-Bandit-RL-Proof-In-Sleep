import BanditRLProof.IndependenceFoundation
import BanditRLProof.KernelIndependentExtension
import BanditRLProof.KernelTrajectoryPrefix
import BanditRLProof.TsallisScheduledIndependentMeanGap

/-!
# IID loss-state producer for scheduled half-Tsallis mean gaps

This module instantiates the abstract scheduled independent-mean contract with
an infinite product of loss states.  The only trajectory-side input is an
explicit finite-prefix kernel factorization: the visible prefix through `n`
must depend on the loss-state stream only through its coordinates through `n`.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- A predictable loss vector obtained by reading one fresh loss state at each
time.  Joint measurability of `value` is the sole evaluation regularity
contract; pointwise bounds make this a valid `[0,1]` loss process. -/
def iidLossStatePredictableLossVector
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState] [MeasurableSpace Action]
    (value : LossState -> Action -> Real)
    (hvalue : Measurable (fun input : LossState × Action =>
      value input.1 input.2))
    (hvalue_nonneg : ∀ state action, 0 <= value state action)
    (hvalue_le_one : ∀ state action, value state action <= 1) :
    Exp3.PredictableLossVector (Nat -> LossState) Action where
  initial environment action := value (environment 0) action
  successor n environment _history action := value (environment (n + 1)) action
  measurable_initial := by
    have hstate : Measurable (fun input : (Nat -> LossState) × Action =>
        input.1 0) := (measurable_pi_apply 0).comp measurable_fst
    have haction : Measurable (fun input : (Nat -> LossState) × Action =>
        input.2) := measurable_snd
    exact hvalue.comp (hstate.prodMk haction)
  measurable_successor n := by
    have hstate : Measurable (fun input :
        (Nat -> LossState) ×
          (History.FinitePairHistory Action Real n × Action) =>
        input.1 (n + 1)) :=
      (measurable_pi_apply (n + 1)).comp measurable_fst
    have haction : Measurable (fun input :
        (Nat -> LossState) ×
          (History.FinitePairHistory Action Real n × Action) =>
        input.2.2) := measurable_snd.comp measurable_snd
    exact hvalue.comp (hstate.prodMk haction)
  initial_nonneg environment action := hvalue_nonneg (environment 0) action
  initial_le_one environment action := hvalue_le_one (environment 0) action
  successor_nonneg n environment _history action :=
    hvalue_nonneg (environment (n + 1)) action
  successor_le_one n environment _history action :=
    hvalue_le_one (environment (n + 1)) action

@[simp]
theorem predictableLossAt_iidLossStatePredictableLossVector
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState] [MeasurableSpace Action]
    (value : LossState -> Action -> Real)
    (hvalue : Measurable (fun input : LossState × Action =>
      value input.1 input.2))
    (hvalue_nonneg : ∀ state action, 0 <= value state action)
    (hvalue_le_one : ∀ state action, value state action <= 1)
    (t : Nat) (sample : (Nat -> LossState) ×
      ((k : Nat) -> Action × Real)) (action : Action) :
    Exp3.predictableLossAt
        (iidLossStatePredictableLossVector value hvalue
          hvalue_nonneg hvalue_le_one) t sample action =
      value (sample.1 t) action := by
  cases t <;> simp [Exp3.predictableLossAt,
    iidLossStatePredictableLossVector]

/-- Extend a finite loss-state prefix to an infinite stream by a fixed fallback
state after the prefix endpoint. -/
def extendLossStatePrefix
    {LossState : Type u} (fallback : LossState) (n : Nat)
    (statePrefix : (i : Finset.Iic n) -> LossState) : Nat -> LossState :=
  fun t => if h : t <= n then
    statePrefix ⟨t, Finset.mem_Iic.mpr h⟩ else fallback

theorem measurable_extendLossStatePrefix
    {LossState : Type u} [MeasurableSpace LossState]
    (fallback : LossState) (n : Nat) :
    Measurable (extendLossStatePrefix fallback n) := by
  exact measurable_pi_lambda _ (fun t => by
    by_cases ht : t <= n
    · simpa [extendLossStatePrefix, ht] using
        (measurable_pi_apply
          (⟨t, Finset.mem_Iic.mpr ht⟩ : Finset.Iic n))
    · simp [extendLossStatePrefix, ht])

@[simp]
theorem extendLossStatePrefix_apply_of_le
    {LossState : Type u} (fallback : LossState) (n t : Nat)
    (ht : t <= n) (statePrefix : (i : Finset.Iic n) -> LossState) :
    extendLossStatePrefix fallback n statePrefix t =
      statePrefix ⟨t, Finset.mem_Iic.mpr ht⟩ := by
  simp [extendLossStatePrefix, ht]

/-- The visible scheduled trajectory prefix generated from an IID loss-state
stream is unchanged when the stream is replaced by any other stream with the
same finite loss-state prefix. -/
theorem sampledScheduledHalfTsallisTrajectoryKernel_map_frestrictLe_eq_of_iidLossState_prefix_eq
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState] [StandardBorelSpace LossState]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (value : LossState -> Action -> Real)
    (hvalue : Measurable (fun input : LossState × Action =>
      value input.1 input.2))
    (hvalue_nonneg : ∀ state action, 0 <= value state action)
    (hvalue_le_one : ∀ state action, value state action <= 1)
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta)
    (environment₁ environment₂ : Nat -> LossState) (n : Nat)
    (henvironment : Preorder.frestrictLe n environment₁ =
      Preorder.frestrictLe n environment₂) :
    (sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector
        (iidLossStatePredictableLossVector value hvalue
          hvalue_nonneg hvalue_le_one).environment environment₁).map
        (Preorder.frestrictLe n) =
      (sampledScheduledHalfTsallisTrajectoryKernel
        arms harms eta selector
          (iidLossStatePredictableLossVector value hvalue
            hvalue_nonneg hvalue_le_one).environment environment₂).map
        (Preorder.frestrictLe n) := by
  let loss := iidLossStatePredictableLossVector value hvalue
    hvalue_nonneg hvalue_le_one
  let algorithm := sampledScheduledHalfTsallisHistoryAlgorithm
    arms harms eta selector
  have hcoordinate : ∀ t, t <= n -> environment₁ t = environment₂ t := by
    intro t ht
    have h := congrFun henvironment
      (⟨t, Finset.mem_Iic.mpr ht⟩ : Finset.Iic n)
    simpa [Preorder.frestrictLe_apply] using h
  have hinitialFeedback :
      (loss.environment.at environment₁).initialFeedback =
        (loss.environment.at environment₂).initialFeedback := by
    ext action event hevent
    simp [loss, Thompson.MeasurableHistoryEnvironment.at,
      Exp3.PredictableLossVector.environment, Kernel.comap_apply,
      Kernel.deterministic_apply, iidLossStatePredictableLossVector,
      hcoordinate 0 (Nat.zero_le n)]
  have hfeedback : ∀ k, k < n ->
      (loss.environment.at environment₁).feedback k =
        (loss.environment.at environment₂).feedback k := by
    intro k hk
    ext input event hevent
    simp [loss, Thompson.MeasurableHistoryEnvironment.at,
      Exp3.PredictableLossVector.environment, Kernel.comap_apply,
      Kernel.deterministic_apply, iidLossStatePredictableLossVector,
      hcoordinate (k + 1) (Nat.succ_le_of_lt hk)]
  rw [sampledScheduledHalfTsallisTrajectoryKernel,
    Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical,
    Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical]
  apply KernelTrajectoryPrefix.trajMeasure_map_frestrictLe_congr
  · rw [hinitialFeedback]
  · intro k hk
    unfold Thompson.historyStepKernel
    rw [hfeedback k hk]

/-- Finite pair-prefix kernel obtained by extending the supplied loss-state
prefix and running the canonical scheduled trajectory. -/
noncomputable def sampledScheduledHalfTsallisIIDPrefixKernel
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Nonempty Action] [DecidableEq Action]
    (fallback : LossState)
    (value : LossState -> Action -> Real)
    (hvalue : Measurable (fun input : LossState × Action =>
      value input.1 input.2))
    (hvalue_nonneg : ∀ state action, 0 <= value state action)
    (hvalue_le_one : ∀ state action, value state action <= 1)
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) (n : Nat) :
    Kernel ((i : Finset.Iic n) -> LossState)
      (History.FinitePairHistory Action Real n) :=
  ((sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector
        (iidLossStatePredictableLossVector value hvalue
          hvalue_nonneg hvalue_le_one).environment).comap
      (extendLossStatePrefix fallback n)
      (measurable_extendLossStatePrefix fallback n)).map
    (Preorder.frestrictLe n)

instance instSampledScheduledHalfTsallisIIDPrefixKernelIsMarkov
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Nonempty Action] [DecidableEq Action]
    (fallback : LossState)
    (value : LossState -> Action -> Real)
    (hvalue : Measurable (fun input : LossState × Action =>
      value input.1 input.2))
    (hvalue_nonneg : ∀ state action, 0 <= value state action)
    (hvalue_le_one : ∀ state action, value state action <= 1)
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) (n : Nat) :
    IsMarkovKernel
      (sampledScheduledHalfTsallisIIDPrefixKernel fallback value hvalue
        hvalue_nonneg hvalue_le_one arms harms eta selector n) := by
  unfold sampledScheduledHalfTsallisIIDPrefixKernel
  letI : IsMarkovKernel
      ((sampledScheduledHalfTsallisTrajectoryKernel
          arms harms eta selector
            (iidLossStatePredictableLossVector value hvalue
              hvalue_nonneg hvalue_le_one).environment).comap
        (extendLossStatePrefix fallback n)
        (measurable_extendLossStatePrefix fallback n)) :=
    by infer_instance
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
    (Preorder.measurable_frestrictLe n)

/-- The stationary mean loss gap induced by one coordinate law. -/
noncomputable def iidLossStateMeanGap
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState]
    (law : Measure LossState) (value : LossState -> Action -> Real)
    (best action : Action) : Real :=
  ∫ state, value state action - value state best ∂law

/-- Exact remaining trajectory-law obligation for the IID route.  At every
scheduled successor time, the generated visible pair prefix is a Markov-kernel
extension of the corresponding finite loss-state prefix. -/
def HasScheduledIIDPrefixKernelFactorization
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState] [MeasurableSpace Action]
    (trajectoryKernel : Kernel (Nat -> LossState)
      ((k : Nat) -> Action × Real))
    (horizon : Nat) : Prop :=
  ∀ n, n + 1 <= horizon ->
    ∃ prefixKernel : Kernel
        ((i : Finset.Iic n) -> LossState)
        (History.FinitePairHistory Action Real n),
      IsMarkovKernel prefixKernel ∧
        trajectoryKernel.map (Preorder.frestrictLe n) =
          prefixKernel.comap (Preorder.frestrictLe n)
            (Preorder.measurable_frestrictLe n)

/-- The canonical scheduled half-Tsallis trajectory automatically factors
through every finite IID loss-state prefix. -/
theorem hasScheduledIIDPrefixKernelFactorization_sampledScheduledHalfTsallisTrajectoryKernel
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState] [StandardBorelSpace LossState]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (fallback : LossState)
    (value : LossState -> Action -> Real)
    (hvalue : Measurable (fun input : LossState × Action =>
      value input.1 input.2))
    (hvalue_nonneg : ∀ state action, 0 <= value state action)
    (hvalue_le_one : ∀ state action, value state action <= 1)
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (selector : HalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta) (horizon : Nat) :
    HasScheduledIIDPrefixKernelFactorization
      (sampledScheduledHalfTsallisTrajectoryKernel
        arms harms eta selector
          (iidLossStatePredictableLossVector value hvalue
            hvalue_nonneg hvalue_le_one).environment)
      horizon := by
  intro n _hn
  let prefixKernel := sampledScheduledHalfTsallisIIDPrefixKernel
    fallback value hvalue hvalue_nonneg hvalue_le_one
      arms harms eta selector n
  refine ⟨prefixKernel, ?_, ?_⟩
  · exact instSampledScheduledHalfTsallisIIDPrefixKernelIsMarkov
      fallback value hvalue hvalue_nonneg hvalue_le_one
        arms harms eta selector n
  · ext environment event hevent
    rw [Kernel.map_apply' _ (Preorder.measurable_frestrictLe n)
        environment hevent,
      Kernel.comap_apply,
      show prefixKernel = sampledScheduledHalfTsallisIIDPrefixKernel
        fallback value hvalue hvalue_nonneg hvalue_le_one
          arms harms eta selector n from rfl,
      sampledScheduledHalfTsallisIIDPrefixKernel,
      Kernel.map_apply' _ (Preorder.measurable_frestrictLe n)
        (Preorder.frestrictLe n environment) hevent,
      Kernel.comap_apply]
    have hprefix : Preorder.frestrictLe n environment =
        Preorder.frestrictLe n
          (extendLossStatePrefix fallback n
            (Preorder.frestrictLe n environment)) := by
      funext i
      simp [Preorder.frestrictLe_apply,
        extendLossStatePrefix_apply_of_le fallback n i.1
          (Finset.mem_Iic.mp i.2)]
    have hmap := congrArg (fun measure => measure event)
      (sampledScheduledHalfTsallisTrajectoryKernel_map_frestrictLe_eq_of_iidLossState_prefix_eq
        value hvalue hvalue_nonneg hvalue_le_one arms harms eta selector
          environment
          (extendLossStatePrefix fallback n
            (Preorder.frestrictLe n environment)) n hprefix)
    dsimp only at hmap
    rw [Measure.map_apply (μ :=
          sampledScheduledHalfTsallisTrajectoryKernel
            arms harms eta selector
              (iidLossStatePredictableLossVector value hvalue
                hvalue_nonneg hvalue_le_one).environment environment)
          (Preorder.measurable_frestrictLe n) hevent,
      Measure.map_apply (μ :=
          sampledScheduledHalfTsallisTrajectoryKernel
            arms harms eta selector
              (iidLossStatePredictableLossVector value hvalue
                hvalue_nonneg hvalue_le_one).environment
            (extendLossStatePrefix fallback n
              (Preorder.frestrictLe n environment)))
          (Preorder.measurable_frestrictLe n) hevent] at hmap
    exact hmap

/-- Infinite-product loss states plus finite-prefix factorization produce the
independence and global-mean contract consumed by scheduled self-bounding. -/
theorem hasScheduledIndependentMeanGapLaw_of_iidLossState
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState] [StandardBorelSpace LossState]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (law : Measure LossState) [IsProbabilityMeasure law]
    (value : LossState -> Action -> Real)
    (hvalue : Measurable (fun input : LossState × Action =>
      value input.1 input.2))
    (hvalue_nonneg : ∀ state action, 0 <= value state action)
    (hvalue_le_one : ∀ state action, value state action <= 1)
    (arms : Finset Action) (best : Action) (horizon : Nat)
    (trajectoryKernel : Kernel (Nat -> LossState)
      ((k : Nat) -> Action × Real))
    [IsMarkovKernel trajectoryKernel]
    (hfactor : HasScheduledIIDPrefixKernelFactorization
      trajectoryKernel horizon) :
    let prior := Measure.infinitePi (fun _ : Nat => law)
    let mu := prior ⊗ₘ trajectoryKernel
    HasScheduledIndependentMeanGapLaw mu arms
      (iidLossStatePredictableLossVector value hvalue
        hvalue_nonneg hvalue_le_one)
      best (iidLossStateMeanGap law value best) horizon := by
  dsimp only
  let prior : Measure (Nat -> LossState) :=
    Measure.infinitePi (fun _ : Nat => law)
  let mu : Measure ((Nat -> LossState) ×
      ((k : Nat) -> Action × Real)) := prior ⊗ₘ trajectoryKernel
  let loss := iidLossStatePredictableLossVector value hvalue
    hvalue_nonneg hvalue_le_one
  have hcoord : iIndepFun
      (fun t (environment : Nat -> LossState) => environment t) prior := by
    simpa only [prior] using
      (IndependenceFoundation.iIndepFun_rewardTrace_infinitePi
        (fun _ : Nat => law))
  intro t ht action _haction
  let lossDiff := fun sample : (Nat -> LossState) ×
      ((k : Nat) -> Action × Real) =>
    Exp3.predictableLossAt loss t sample action -
      Exp3.predictableLossAt loss t sample best
  constructor
  · cases t with
    | zero =>
        change Indep (MeasurableSpace.comap lossDiff inferInstance) ⊥ mu
        exact indep_bot_right _
    | succ n =>
        rcases hfactor n ht with ⟨prefixKernel, hprefixMarkov, hprefix⟩
        letI : IsMarkovKernel prefixKernel := hprefixMarkov
        let currentDiff := fun environment : Nat -> LossState =>
          value (environment (n + 1)) action -
            value (environment (n + 1)) best
        let pastEnvironment := fun environment : Nat -> LossState =>
          Preorder.frestrictLe n environment
        let visiblePrefix := fun trajectory : (k : Nat) -> Action × Real =>
          Preorder.frestrictLe n trajectory
        have hcurrentDiff : Measurable currentDiff := by
          have hstate : Measurable (fun environment : Nat -> LossState =>
              environment (n + 1)) := measurable_pi_apply (n + 1)
          have hactionValue : Measurable (fun environment : Nat -> LossState =>
              value (environment (n + 1)) action) :=
            hvalue.comp (hstate.prodMk measurable_const)
          have hbestValue : Measurable (fun environment : Nat -> LossState =>
              value (environment (n + 1)) best) :=
            hvalue.comp (hstate.prodMk measurable_const)
          exact hactionValue.sub hbestValue
        have hpastEnvironment : Measurable pastEnvironment :=
          Preorder.measurable_frestrictLe n
        have hvisiblePrefix : Measurable visiblePrefix :=
          Preorder.measurable_frestrictLe n
        have hcoordPast : IndepFun currentDiff pastEnvironment prior := by
          let currentSet : Finset Nat := {n + 1}
          let pastSet : Finset Nat := Finset.Iic n
          have hdisjoint : Disjoint currentSet pastSet := by
            rw [Finset.disjoint_left]
            intro i hiCurrent hiPast
            have hi : i = n + 1 := Finset.mem_singleton.mp hiCurrent
            subst i
            exact (Nat.not_succ_le_self n) (Finset.mem_Iic.mp hiPast)
          have htuples := hcoord.indepFun_finset currentSet pastSet
            hdisjoint (fun _ => measurable_pi_apply _)
          let currentIndex : currentSet :=
            ⟨n + 1, Finset.mem_singleton_self _⟩
          let readCurrent := fun states : (i : currentSet) -> LossState =>
            value (states currentIndex) action -
              value (states currentIndex) best
          have hreadCurrent : Measurable readCurrent := by
            have hstate : Measurable
                (fun states : (i : currentSet) -> LossState =>
                  states currentIndex) := measurable_pi_apply currentIndex
            exact
              (hvalue.comp (hstate.prodMk measurable_const)).sub
                (hvalue.comp (hstate.prodMk measurable_const))
          have hcomposed := htuples.comp hreadCurrent measurable_id
          simpa only [currentDiff, pastEnvironment, currentSet, pastSet,
            Preorder.frestrictLe_apply] using hcomposed
        have hextended :=
          indepFun_fst_snd_compProd_comap_of_indepFun
            prior currentDiff hcurrentDiff pastEnvironment hpastEnvironment
              prefixKernel hcoordPast
        let joinPrefix := fun sample : (Nat -> LossState) ×
            ((k : Nat) -> Action × Real) =>
          (sample.1, visiblePrefix sample.2)
        have hjoinPrefix : Measurable joinPrefix :=
          measurable_fst.prodMk (hvisiblePrefix.comp measurable_snd)
        have hmap : mu.map joinPrefix =
            prior ⊗ₘ prefixKernel.comap pastEnvironment hpastEnvironment := by
          calc
            mu.map joinPrefix =
                prior ⊗ₘ trajectoryKernel.map visiblePrefix := by
              symm
              simpa only [mu, joinPrefix, visiblePrefix] using
                (Measure.compProd_map
                  (μ := prior) (κ := trajectoryKernel) hvisiblePrefix)
            _ = prior ⊗ₘ
                prefixKernel.comap pastEnvironment hpastEnvironment := by
              rw [hprefix]
        have honMap : IndepFun (currentDiff ∘ Prod.fst) Prod.snd
            (mu.map joinPrefix) := by
          rw [hmap]
          exact hextended
        have hpulled := IndepFun.comp_of_map hjoinPrefix
          (hcurrentDiff.comp measurable_fst) measurable_snd honMap
        change IndepFun lossDiff
          (fun sample : (Nat -> LossState) ×
            ((k : Nat) -> Action × Real) => visiblePrefix sample.2) mu
        simpa only [lossDiff, loss, currentDiff, visiblePrefix,
          Function.comp_apply,
          predictableLossAt_iidLossStatePredictableLossVector] using hpulled
  · have hstateDiff : Measurable (fun state : LossState =>
        value state action - value state best) :=
      (hvalue.comp (measurable_id.prodMk measurable_const)).sub
        (hvalue.comp (measurable_id.prodMk measurable_const))
    calc
      integral mu lossDiff =
          integral mu (fun sample =>
            value (sample.1 t) action - value (sample.1 t) best) := by
        congr 1
        funext sample
        simp only [lossDiff, loss,
          predictableLossAt_iidLossStatePredictableLossVector]
      _ = integral (mu.map Prod.fst) (fun environment : Nat -> LossState =>
            value (environment t) action - value (environment t) best) := by
        exact (integral_map
          (μ := mu) (φ := Prod.fst)
          (f := fun environment : Nat -> LossState =>
            value (environment t) action - value (environment t) best)
          measurable_fst.aemeasurable
          (hstateDiff.comp
            (measurable_pi_apply t)).aestronglyMeasurable).symm
      _ = integral prior (fun environment : Nat -> LossState =>
            value (environment t) action - value (environment t) best) := by
        have hfst : mu.map Prod.fst = prior := by
          change (prior ⊗ₘ trajectoryKernel).fst = prior
          exact Measure.fst_compProd prior trajectoryKernel
        rw [hfst]
      _ = integral (prior.map (fun environment : Nat -> LossState =>
            environment t)) (fun state : LossState =>
              value state action - value state best) := by
        exact (integral_map
          (μ := prior) (φ := fun environment : Nat -> LossState =>
            environment t)
          (f := fun state : LossState =>
            value state action - value state best)
          (measurable_pi_apply t).aemeasurable
          hstateDiff.aestronglyMeasurable).symm
      _ = integral law (fun state : LossState =>
            value state action - value state best) := by
        rw [show prior = Measure.infinitePi (fun _ : Nat => law) from rfl,
          Measure.infinitePi_map_eval]
      _ = iidLossStateMeanGap law value best action := rfl

/-- The canonical scheduled half-Tsallis trajectory reaches the explicit
logarithmic bound for an IID loss-state environment.  Its finite-prefix
factorization is constructed internally. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_log_iidLossState
    {LossState : Type u} {Action : Type v}
    [MeasurableSpace LossState] [StandardBorelSpace LossState]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (law : Measure LossState) [IsProbabilityMeasure law]
    (value : LossState -> Action -> Real)
    (hvalue : Measurable (fun input : LossState × Action =>
      value input.1 input.2))
    (hvalue_nonneg : ∀ state action, 0 <= value state action)
    (hvalue_le_one : ∀ state action, value state action <= 1)
    (arms : Finset Action) (harms : arms.Nonempty)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (hgapPos : ∀ action, action ∈ arms.erase best ->
      0 < iidLossStateMeanGap law value best action)
    (corruption : Real) (hcorruption : 0 <= corruption) :
    let prior := Measure.infinitePi (fun _ : Nat => law)
    let loss := iidLossStatePredictableLossVector value hvalue
      hvalue_nonneg hvalue_le_one
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms sampledScheduledHalfTsallisSqrtSchedule
        selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass best) horizon) <=
      (1 + Real.log (((horizon + 1 : Nat) : Real))) *
        (1 + 25 * (arms.erase best).sum (fun action =>
          1 / iidLossStateMeanGap law value best action)) + corruption := by
  dsimp only
  letI : Nonempty LossState := nonempty_of_isProbabilityMeasure law
  let loss := iidLossStatePredictableLossVector value hvalue
    hvalue_nonneg hvalue_le_one
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms sampledScheduledHalfTsallisSqrtSchedule loss
  let trajectoryKernel := sampledScheduledHalfTsallisTrajectoryKernel
    arms harms sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
  have hfactor : HasScheduledIIDPrefixKernelFactorization trajectoryKernel
      horizon := by
    simpa only [trajectoryKernel, selector, loss] using
      hasScheduledIIDPrefixKernelFactorization_sampledScheduledHalfTsallisTrajectoryKernel
        (Classical.ofNonempty : LossState) value hvalue hvalue_nonneg
          hvalue_le_one arms harms sampledScheduledHalfTsallisSqrtSchedule
            selector.finiteHistory horizon
  have hgapLaw :
      let prior := Measure.infinitePi (fun _ : Nat => law)
      let mu := prior ⊗ₘ trajectoryKernel
      HasScheduledIndependentMeanGapLaw mu arms loss best
        (iidLossStateMeanGap law value best) horizon := by
    simpa only [loss, trajectoryKernel, selector] using
      hasScheduledIndependentMeanGapLaw_of_iidLossState
        law value hvalue hvalue_nonneg hvalue_le_one arms best horizon
          trajectoryKernel hfactor
  simpa only [loss, selector, trajectoryKernel] using
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_log_independentMeanGap
      (Measure.infinitePi (fun _ : Nat => law)) arms harms loss hbest horizon
        (iidLossStateMeanGap law value best) hgapPos hgapLaw
          corruption hcorruption

end Tsallis
end BanditRLProof
