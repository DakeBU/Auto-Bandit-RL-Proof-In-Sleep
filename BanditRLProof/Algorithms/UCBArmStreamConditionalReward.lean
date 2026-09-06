import BanditRLProof.Algorithms.UCBRealStationaryExplicitPolicy
import BanditRLProof.Algorithms.UCBArmStreamTail
import Mathlib.Probability.Independence.InfinitePi

/-!
# Conditional laws for stationary UCB arm-stream coordinates

This module isolates the product-measure part of the selected-reward route.
Every `(pull index, arm)` coordinate is independent of the function containing
all other coordinates, so its conditional distribution given that complement
is the prescribed stationary arm law.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory

namespace UCB

/-- A flattened pull-index/arm coordinate of a latent arm-reward stream. -/
def armStreamCoordinate {K : Nat} (index : Nat × Fin K) :
    ArmRewardStream K -> Real :=
  fun stream => stream index.1 index.2

/-- The latent arm stream with one specified coordinate omitted. -/
def armStreamWithoutCoordinate {K : Nat} (target : Nat × Fin K) :
    ArmRewardStream K -> ({index : Nat × Fin K // index ≠ target} -> Real) :=
  fun stream index => armStreamCoordinate index.1 stream

/-- Reconstruct a latent arm stream after supplying one omitted coordinate. -/
def armStreamInsertCoordinate {K : Nat} (target : Nat × Fin K) (value : Real) :
    ({index : Nat × Fin K // index ≠ target} -> Real) -> ArmRewardStream K :=
  fun rest index arm =>
    if hindex : (index, arm) = target then value
    else rest ⟨(index, arm), hindex⟩

/-- The history/action condition used by the successor reward kernel. -/
noncomputable def armStreamHistoryAction
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat) :
    ArmRewardStream K ->
      History.FinitePairHistory (Fin K) Real n × Fin K :=
  fun stream =>
    let history := armStreamHistory hK c stream n
    (history, realHistoryNextArm hK c n history)

/-- The next unused pull-index/arm coordinate selected after history `n`. -/
noncomputable def armStreamNextCoordinate
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat) :
    ArmRewardStream K -> Nat × Fin K :=
  fun stream =>
    let condition := armStreamHistoryAction hK c n stream
    (ETC.realHistoryPullCount n condition.1 condition.2, condition.2)

/-- The pull-index/arm coordinate encoded by a successor history/action condition. -/
noncomputable def armStreamCoordinateOfHistoryAction
    {K : Nat} (n : Nat) :
    History.FinitePairHistory (Fin K) Real n × Fin K -> Nat × Fin K :=
  fun condition =>
    (ETC.realHistoryPullCount n condition.1 condition.2, condition.2)

/-- Conditions that encode one fixed next pull-index/arm coordinate. -/
def armStreamHistoryActionCoordinateBranch
    {K : Nat} (n : Nat) (target : Nat × Fin K) :
    Set (History.FinitePairHistory (Fin K) Real n × Fin K) :=
  {condition | armStreamCoordinateOfHistoryAction n condition = target}

/-- The stationary reward kernel selected by the arm component of a condition. -/
noncomputable abbrev armStreamSelectedRewardKernel
    {K : Nat} (n : Nat) (nu : Kernel (Fin K) Real) :
    Kernel (History.FinitePairHistory (Fin K) Real n × Fin K) Real :=
  nu.comap Prod.snd measurable_snd

/-- Latent streams for which one fixed pull-index/arm coordinate is selected next. -/
def armStreamNextCoordinateBranch
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (target : Nat × Fin K) : Set (ArmRewardStream K) :=
  {stream | armStreamNextCoordinate hK c n stream = target}

/-- Reconstructed successor condition using only a fixed coordinate's complement. -/
noncomputable def armStreamHistoryActionFromWithout
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (target : Nat × Fin K) (value : Real) :
    ({index : Nat × Fin K // index ≠ target} -> Real) ->
      History.FinitePairHistory (Fin K) Real n × Fin K :=
  armStreamHistoryAction hK c n ∘ armStreamInsertCoordinate target value

theorem measurable_armStreamCoordinate
    {K : Nat} (index : Nat × Fin K) :
    Measurable (armStreamCoordinate index) := by
  exact (measurable_pi_apply index.2).comp (measurable_pi_apply index.1)

theorem measurable_armStreamWithoutCoordinate
    {K : Nat} (target : Nat × Fin K) :
    Measurable (armStreamWithoutCoordinate target) := by
  exact measurable_pi_lambda _ fun index =>
    measurable_armStreamCoordinate index.1

theorem measurable_armStreamInsertCoordinate
    {K : Nat} (target : Nat × Fin K) (value : Real) :
    Measurable (armStreamInsertCoordinate target value) := by
  apply measurable_pi_lambda
  intro index
  apply measurable_pi_lambda
  intro arm
  by_cases hindex : (index, arm) = target
  · simp [armStreamInsertCoordinate, hindex]
  · simpa [armStreamInsertCoordinate, hindex] using
      (measurable_pi_apply
        (⟨(index, arm), hindex⟩ :
          {candidate : Nat × Fin K // candidate ≠ target}))

@[simp]
theorem armStreamWithoutCoordinate_insertCoordinate
    {K : Nat} (target : Nat × Fin K) (value : Real)
    (rest : {index : Nat × Fin K // index ≠ target} -> Real) :
    armStreamWithoutCoordinate target
        (armStreamInsertCoordinate target value rest) = rest := by
  funext index
  simp [armStreamWithoutCoordinate, armStreamCoordinate,
    armStreamInsertCoordinate, index.2]

theorem measurable_armStreamHistoryAction
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat) :
    Measurable (armStreamHistoryAction hK c n) := by
  have hhistory := measurable_armStreamHistory hK c n
  have harm := (measurable_realHistoryNextArm hK c n).comp hhistory
  simpa [armStreamHistoryAction] using hhistory.prodMk harm

theorem measurable_armStreamNextCoordinate
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat) :
    Measurable (armStreamNextCoordinate hK c n) := by
  have hcountEval : Measurable
      (fun input : History.FinitePairHistory (Fin K) Real n × Fin K =>
        ETC.realHistoryPullCount n input.1 input.2) := by
    apply measurable_from_prod_countable_left
    intro arm
    exact measurable_realHistoryPullCount n arm
  have hcondition := measurable_armStreamHistoryAction hK c n
  have hcount := hcountEval.comp hcondition
  simpa [armStreamNextCoordinate] using hcount.prodMk hcondition.snd

theorem measurable_armStreamCoordinateOfHistoryAction
    {K : Nat} (n : Nat) :
    Measurable (armStreamCoordinateOfHistoryAction (K := K) n) := by
  have hcountEval : Measurable
      (fun input : History.FinitePairHistory (Fin K) Real n × Fin K =>
        ETC.realHistoryPullCount n input.1 input.2) := by
    apply measurable_from_prod_countable_left
    intro arm
    exact measurable_realHistoryPullCount n arm
  simpa [armStreamCoordinateOfHistoryAction] using
    hcountEval.prodMk measurable_snd

theorem measurableSet_armStreamHistoryActionCoordinateBranch
    {K : Nat} (n : Nat) (target : Nat × Fin K) :
    MeasurableSet (armStreamHistoryActionCoordinateBranch n target) := by
  exact measurableSet_eq_fun
    (measurable_armStreamCoordinateOfHistoryAction n) measurable_const

theorem measurableSet_armStreamNextCoordinateBranch
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (target : Nat × Fin K) :
    MeasurableSet (armStreamNextCoordinateBranch hK c n target) := by
  exact measurableSet_eq_fun
    (measurable_armStreamNextCoordinate hK c n) measurable_const

theorem armStreamNextCoordinate_eq_coordinateOfHistoryAction
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (stream : ArmRewardStream K) :
    armStreamNextCoordinate hK c n stream =
      armStreamCoordinateOfHistoryAction n
        (armStreamHistoryAction hK c n stream) := by
  rfl

theorem pairwise_disjoint_armStreamHistoryActionCoordinateBranch
    {K : Nat} (n : Nat) :
    Pairwise (Function.onFun
      (fun s t : Set
        (History.FinitePairHistory (Fin K) Real n × Fin K) => Disjoint s t)
      (fun target : Nat × Fin K =>
        armStreamHistoryActionCoordinateBranch n target)) := by
  intro target target' hne
  change Disjoint
    (armStreamHistoryActionCoordinateBranch n target)
    (armStreamHistoryActionCoordinateBranch n target')
  rw [Set.disjoint_left]
  intro condition htarget htarget'
  apply hne
  exact htarget.symm.trans htarget'

theorem pairwise_disjoint_armStreamNextCoordinateBranch
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat) :
    Pairwise (Function.onFun
      (fun s t : Set (ArmRewardStream K) => Disjoint s t)
      (fun target : Nat × Fin K =>
        armStreamNextCoordinateBranch hK c n target)) := by
  intro target target' hne
  change Disjoint
    (armStreamNextCoordinateBranch hK c n target)
    (armStreamNextCoordinateBranch hK c n target')
  rw [Set.disjoint_left]
  intro stream htarget htarget'
  apply hne
  exact htarget.symm.trans htarget'

theorem iUnion_armStreamHistoryActionCoordinateBranch
    {K : Nat} (n : Nat) :
    (⋃ target : Nat × Fin K,
      armStreamHistoryActionCoordinateBranch n target) = Set.univ := by
  ext condition
  simp [armStreamHistoryActionCoordinateBranch]

theorem iUnion_armStreamNextCoordinateBranch
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat) :
    (⋃ target : Nat × Fin K,
      armStreamNextCoordinateBranch hK c n target) = Set.univ := by
  ext stream
  simp [armStreamNextCoordinateBranch]

theorem measure_eq_sum_restrict_armStreamHistoryActionCoordinateBranch
    {K : Nat} (n : Nat)
    (mu : Measure
      (History.FinitePairHistory (Fin K) Real n × Fin K)) :
    mu = Measure.sum fun target : Nat × Fin K =>
      mu.restrict (armStreamHistoryActionCoordinateBranch n target) := by
  rw [← Measure.restrict_iUnion
    (pairwise_disjoint_armStreamHistoryActionCoordinateBranch n)
    (measurableSet_armStreamHistoryActionCoordinateBranch n),
    iUnion_armStreamHistoryActionCoordinateBranch n,
    Measure.restrict_univ]

theorem armStreamMeasure_eq_sum_restrict_nextCoordinateBranch
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    armStreamMeasure nu = Measure.sum fun target : Nat × Fin K =>
      (armStreamMeasure nu).restrict
        (armStreamNextCoordinateBranch hK c n target) := by
  rw [← Measure.restrict_iUnion
    (pairwise_disjoint_armStreamNextCoordinateBranch hK c n)
    (measurableSet_armStreamNextCoordinateBranch hK c n),
    iUnion_armStreamNextCoordinateBranch hK c n,
    Measure.restrict_univ]

theorem measurable_armStreamHistoryActionFromWithout
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (target : Nat × Fin K) (value : Real) :
    Measurable (armStreamHistoryActionFromWithout hK c n target value) := by
  exact (measurable_armStreamHistoryAction hK c n).comp
    (measurable_armStreamInsertCoordinate target value)

/-- The first component of the next coordinate is the selected arm's current count. -/
theorem armStreamNextCoordinate_fst_eq_pullCount
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) (n : Nat) :
    (armStreamNextCoordinate hK c n stream).1 =
      pullCount (armStreamAction hK c stream)
        (armStreamNextCoordinate hK c n stream).2 (n + 1) := by
  simp only [armStreamNextCoordinate, armStreamHistoryAction]
  rw [armStreamHistory_eq_finitePairHistoryOfTrace]
  exact ETC.realHistoryPullCount_finitePairHistoryOfTrace _ _ n _

/-- The successor reward reads exactly the next coordinate selected after history `n`. -/
theorem armStreamReward_succ_eq_nextCoordinate
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) (n : Nat) :
    armStreamReward hK c stream (n + 1) =
      armStreamCoordinate (armStreamNextCoordinate hK c n stream) stream := by
  simp only [armStreamReward, rewardFromArmStream, armStreamCoordinate]
  rw [armStreamAction_succ]
  simp only [armStreamNextCoordinate, armStreamHistoryAction]
  rw [armStreamHistory_eq_finitePairHistoryOfTrace]
  rw [ETC.realHistoryPullCount_finitePairHistoryOfTrace]
  rfl

/--
The recursive history through `n` only reads coordinates whose pull index is
strictly below the corresponding arm count at time `n + 1`.
-/
theorem armStreamHistory_eq_of_eq_below_pullCount
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream stream' : ArmRewardStream K) (n : Nat)
    (hagrees : ∀ arm index,
      index < pullCount (armStreamAction hK c stream) arm (n + 1) →
        stream index arm = stream' index arm) :
    armStreamHistory hK c stream n = armStreamHistory hK c stream' n := by
  induction n generalizing stream stream' with
  | zero =>
      have hzero : stream 0 (initializationArm hK 0) =
          stream' 0 (initializationArm hK 0) := by
        apply hagrees
        simp
      simp only [armStreamHistory]
      funext _i
      exact Prod.ext rfl hzero
  | succ n ih =>
      have hprefix : ∀ arm index,
          index < pullCount (armStreamAction hK c stream) arm (n + 1) →
            stream index arm = stream' index arm := by
        intro arm index hindex
        apply hagrees arm index
        exact lt_of_lt_of_le hindex <|
          pullCount_mono (armStreamAction hK c stream) arm (Nat.le_succ _)
      have hhistory := ih stream stream' hprefix
      simp only [armStreamHistory]
      rw [← hhistory]
      apply congrArg (History.extendPairHistorySucc
        (armStreamHistory hK c stream n))
      apply Prod.ext
      · rfl
      · apply hagrees
        rw [armStreamHistory_eq_finitePairHistoryOfTrace]
        rw [ETC.realHistoryPullCount_finitePairHistoryOfTrace]
        have hselected : armStreamAction hK c stream (n + 1) =
            realHistoryNextArm hK c n
              (History.finitePairHistoryOfTrace
                (armStreamAction hK c stream)
                (armStreamReward hK c stream) n) := by
          rw [← armStreamHistory_eq_finitePairHistoryOfTrace]
          exact armStreamAction_succ hK c stream n
        rw [pullCount_succ_of_eq
          (armStreamAction hK c stream) _ (n + 1) hselected]
        exact Nat.lt_succ_self _

/--
Changing one not-yet-consumed coordinate cannot alter the history already
generated from the latent stream.
-/
theorem armStreamHistory_eq_of_withoutCoordinate_eq_of_pullCount_le
    {K : Nat} (hK : 0 < K) (c : Real)
    (target : Nat × Fin K) (stream stream' : ArmRewardStream K) (n : Nat)
    (hwithout : armStreamWithoutCoordinate target stream =
      armStreamWithoutCoordinate target stream')
    (hfuture : pullCount (armStreamAction hK c stream) target.2 (n + 1) ≤
      target.1) :
    armStreamHistory hK c stream n = armStreamHistory hK c stream' n := by
  apply armStreamHistory_eq_of_eq_below_pullCount hK c stream stream' n
  intro arm index hindex
  by_cases htarget : (index, arm) = target
  · have hle : pullCount (armStreamAction hK c stream) arm (n + 1) ≤
        index := by
      simpa [← htarget] using hfuture
    exact (Nat.not_lt_of_ge hle hindex).elim
  · have hcoordinate := congrFun hwithout ⟨(index, arm), htarget⟩
    simpa [armStreamWithoutCoordinate, armStreamCoordinate] using hcoordinate

/--
The event that a fixed coordinate is selected next factors through the stream
with that coordinate omitted.
-/
theorem armStreamNextCoordinate_eq_iff_insertCoordinate
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (target : Nat × Fin K) (value : Real) (stream : ArmRewardStream K) :
    armStreamNextCoordinate hK c n stream = target ↔
      armStreamNextCoordinate hK c n
        (armStreamInsertCoordinate target value
          (armStreamWithoutCoordinate target stream)) = target := by
  let rebuilt := armStreamInsertCoordinate target value
    (armStreamWithoutCoordinate target stream)
  have hwithout : armStreamWithoutCoordinate target stream =
      armStreamWithoutCoordinate target rebuilt := by
    simp [rebuilt]
  constructor
  · intro hnext
    have hcount := armStreamNextCoordinate_fst_eq_pullCount hK c stream n
    rw [hnext] at hcount
    have hhistory :=
      armStreamHistory_eq_of_withoutCoordinate_eq_of_pullCount_le
        hK c target stream rebuilt n hwithout hcount.symm.le
    simpa [armStreamNextCoordinate, armStreamHistoryAction, rebuilt,
      hhistory] using hnext
  · intro hnext
    have hcount := armStreamNextCoordinate_fst_eq_pullCount hK c rebuilt n
    rw [hnext] at hcount
    have hhistory :=
      armStreamHistory_eq_of_withoutCoordinate_eq_of_pullCount_le
        hK c target rebuilt stream n hwithout.symm hcount.symm.le
    simpa [armStreamNextCoordinate, armStreamHistoryAction, rebuilt,
      hhistory] using hnext

/--
On the branch selecting `target`, the actual successor condition equals its
reconstruction from all coordinates except `target`.
-/
theorem armStreamHistoryAction_eq_fromWithout_of_nextCoordinate_eq
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (target : Nat × Fin K) (value : Real) (stream : ArmRewardStream K)
    (hnext : armStreamNextCoordinate hK c n stream = target) :
    armStreamHistoryAction hK c n stream =
      armStreamHistoryActionFromWithout hK c n target value
        (armStreamWithoutCoordinate target stream) := by
  let rebuilt := armStreamInsertCoordinate target value
    (armStreamWithoutCoordinate target stream)
  have hwithout : armStreamWithoutCoordinate target stream =
      armStreamWithoutCoordinate target rebuilt := by
    simp [rebuilt]
  have hcount := armStreamNextCoordinate_fst_eq_pullCount hK c stream n
  rw [hnext] at hcount
  have hhistory :=
    armStreamHistory_eq_of_withoutCoordinate_eq_of_pullCount_le
      hK c target stream rebuilt n hwithout hcount.symm.le
  simp [armStreamHistoryActionFromWithout, armStreamHistoryAction,
    rebuilt, hhistory]

/-- All pull-index/arm coordinates are mutually independent. -/
theorem iIndepFun_armStreamMeasure_coordinate
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    iIndepFun
      (fun index : Nat × Fin K => armStreamCoordinate index)
      (armStreamMeasure nu) := by
  simpa [armStreamMeasure, armStreamCoordinate] using
    (iIndepFun_uncurry_infinitePi'
      (fun _index : Nat => fun arm : Fin K => nu arm)
      (fun _index _arm => measurable_id))

set_option maxHeartbeats 800000 in
/-- A fixed coordinate is independent of the collection of all other coordinates. -/
theorem indepFun_armStreamMeasure_coordinate_without
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (target : Nat × Fin K) :
    IndepFun (armStreamCoordinate target)
      (armStreamWithoutCoordinate target) (armStreamMeasure nu) := by
  let m : (Nat × Fin K) -> MeasurableSpace (ArmRewardStream K) :=
    fun index => MeasurableSpace.comap (armStreamCoordinate index) inferInstance
  have hm_le : forall index,
      m index <= (inferInstance : MeasurableSpace (ArmRewardStream K)) := fun index =>
    (measurable_armStreamCoordinate index).comap_le
  have hindep : iIndep m (armStreamMeasure nu) := by
    exact iIndepFun_armStreamMeasure_coordinate nu
  have hdisjoint : Disjoint ({target} : Set (Nat × Fin K))
      {index | index ≠ target} := by
    simp
  have h := indep_iSup_of_disjoint hm_le hindep hdisjoint
  have hleft :
      (iSup fun index : Nat × Fin K =>
        iSup fun _h : index ∈ ({target} : Set (Nat × Fin K)) => m index) =
        m target := by
    simp
  have hright :
      (iSup fun index : Nat × Fin K =>
        iSup fun _h : index ∈ {candidate | candidate ≠ target} => m index) =
        MeasurableSpace.comap (armStreamWithoutCoordinate target)
          inferInstance := by
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, armStreamWithoutCoordinate,
      Function.comp_def, m]
    apply le_antisymm
    · refine iSup_le fun index => iSup_le fun hindex => ?_
      exact le_iSup_of_le (Subtype.mk index hindex) le_rfl
    · refine iSup_le fun index => ?_
      exact le_iSup_of_le index.1 <| le_iSup_of_le index.2 le_rfl
  change Indep
    (MeasurableSpace.comap (armStreamCoordinate target) inferInstance)
    (MeasurableSpace.comap (armStreamWithoutCoordinate target) inferInstance)
    (armStreamMeasure nu)
  rw [hleft, hright] at h
  exact h

/-- A fixed reward coordinate is independent of the reconstructed successor condition. -/
theorem indepFun_armStreamMeasure_coordinate_historyActionFromWithout
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (target : Nat × Fin K) (value : Real) :
    IndepFun (armStreamCoordinate target)
      (fun stream : ArmRewardStream K =>
        armStreamHistoryActionFromWithout hK c n target value
          (armStreamWithoutCoordinate target stream))
      (armStreamMeasure nu) := by
  have hindep :=
    (indepFun_armStreamMeasure_coordinate_without nu target).comp
      measurable_id
      (measurable_armStreamHistoryActionFromWithout hK c n target value)
  simpa [Function.comp_def] using hindep

/--
The reconstructed successor condition and a fixed omitted coordinate have a
product joint law, with the prescribed arm marginal on the reward coordinate.
-/
theorem armStreamMeasure_map_historyActionFromWithout_coordinate_eq_prod
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (target : Nat × Fin K) (value : Real) :
    Measure.map
        (fun stream : ArmRewardStream K =>
          (armStreamHistoryActionFromWithout hK c n target value
              (armStreamWithoutCoordinate target stream),
            armStreamCoordinate target stream))
        (armStreamMeasure nu) =
      (Measure.map
        (fun stream : ArmRewardStream K =>
          armStreamHistoryActionFromWithout hK c n target value
            (armStreamWithoutCoordinate target stream))
        (armStreamMeasure nu)).prod (nu target.2) := by
  let condition := fun stream : ArmRewardStream K =>
    armStreamHistoryActionFromWithout hK c n target value
      (armStreamWithoutCoordinate target stream)
  have hcondition : Measurable condition :=
    (measurable_armStreamHistoryActionFromWithout hK c n target value).comp
      (measurable_armStreamWithoutCoordinate target)
  have hcoordinate := measurable_armStreamCoordinate target
  have hjoint :=
    (indepFun_iff_map_prod_eq_prod_map_map
      hcondition.aemeasurable hcoordinate.aemeasurable).mp
      (indepFun_armStreamMeasure_coordinate_historyActionFromWithout
        hK c n nu target value).symm
  rw [hjoint]
  congr 1
  simpa [armStreamCoordinate] using
    armStreamMeasure_map_coord nu target.1 target.2

/-- The reconstructed condition is in `target`'s branch exactly on the actual branch. -/
theorem armStreamHistoryActionFromWithout_mem_coordinateBranch_iff
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (target : Nat × Fin K) (value : Real) (stream : ArmRewardStream K) :
    armStreamHistoryActionFromWithout hK c n target value
        (armStreamWithoutCoordinate target stream) ∈
      armStreamHistoryActionCoordinateBranch n target ↔
    stream ∈ armStreamNextCoordinateBranch hK c n target := by
  change armStreamCoordinateOfHistoryAction n
      (armStreamHistoryAction hK c n
        (armStreamInsertCoordinate target value
          (armStreamWithoutCoordinate target stream))) = target ↔
    armStreamNextCoordinate hK c n stream = target
  rw [← armStreamNextCoordinate_eq_coordinateOfHistoryAction hK c n]
  exact (armStreamNextCoordinate_eq_iff_insertCoordinate
    hK c n target value stream).symm

/-- Both actual and reconstructed condition maps induce the same branch restriction. -/
theorem map_historyActionFromWithout_restrict_coordinateBranch_eq_historyAction
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (target : Nat × Fin K) (value : Real)
    (mu : Measure (ArmRewardStream K)) :
    (Measure.map
      (fun stream : ArmRewardStream K =>
        armStreamHistoryActionFromWithout hK c n target value
          (armStreamWithoutCoordinate target stream)) mu).restrict
        (armStreamHistoryActionCoordinateBranch n target) =
      (Measure.map (armStreamHistoryAction hK c n) mu).restrict
        (armStreamHistoryActionCoordinateBranch n target) := by
  have hrebuilt : Measurable
      (fun stream : ArmRewardStream K =>
        armStreamHistoryActionFromWithout hK c n target value
          (armStreamWithoutCoordinate target stream)) :=
    (measurable_armStreamHistoryActionFromWithout hK c n target value).comp
      (measurable_armStreamWithoutCoordinate target)
  have hcondition := measurable_armStreamHistoryAction hK c n
  have hbranch :=
    measurableSet_armStreamHistoryActionCoordinateBranch n target
  rw [Measure.restrict_map hrebuilt hbranch,
    Measure.restrict_map hcondition hbranch]
  have hrebuiltPreimage :
      (fun stream : ArmRewardStream K =>
        armStreamHistoryActionFromWithout hK c n target value
          (armStreamWithoutCoordinate target stream)) ⁻¹'
          armStreamHistoryActionCoordinateBranch n target =
        armStreamNextCoordinateBranch hK c n target := by
    ext stream
    exact armStreamHistoryActionFromWithout_mem_coordinateBranch_iff
      hK c n target value stream
  have hconditionPreimage :
      armStreamHistoryAction hK c n ⁻¹'
          armStreamHistoryActionCoordinateBranch n target =
        armStreamNextCoordinateBranch hK c n target := by
    ext stream
    rfl
  rw [hrebuiltPreimage, hconditionPreimage]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem
    (measurableSet_armStreamNextCoordinateBranch hK c n target)] with
      stream hnext
  exact (armStreamHistoryAction_eq_fromWithout_of_nextCoordinate_eq
    hK c n target value stream hnext).symm

/--
On one fixed next-coordinate branch, the actual successor condition/reward pair
has the restricted condition marginal times the prescribed arm law.
-/
theorem armStreamMeasure_map_historyAction_reward_restrict_branch_eq_prod
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (target : Nat × Fin K) (value : Real) :
    Measure.map
        (fun stream : ArmRewardStream K =>
          (armStreamHistoryAction hK c n stream,
            armStreamReward hK c stream (n + 1)))
        ((armStreamMeasure nu).restrict
          (armStreamNextCoordinateBranch hK c n target)) =
      ((Measure.map (armStreamHistoryAction hK c n)
          (armStreamMeasure nu)).restrict
        (armStreamHistoryActionCoordinateBranch n target)).prod
          (nu target.2) := by
  let rebuiltCondition := fun stream : ArmRewardStream K =>
    armStreamHistoryActionFromWithout hK c n target value
      (armStreamWithoutCoordinate target stream)
  let rebuiltPair := fun stream : ArmRewardStream K =>
    (rebuiltCondition stream, armStreamCoordinate target stream)
  let actualPair := fun stream : ArmRewardStream K =>
    (armStreamHistoryAction hK c n stream,
      armStreamReward hK c stream (n + 1))
  let streamBranch := armStreamNextCoordinateBranch hK c n target
  let conditionBranch := armStreamHistoryActionCoordinateBranch n target
  have hstreamBranch : MeasurableSet streamBranch :=
    measurableSet_armStreamNextCoordinateBranch hK c n target
  have hconditionBranch : MeasurableSet conditionBranch :=
    measurableSet_armStreamHistoryActionCoordinateBranch n target
  have hrebuiltCondition : Measurable rebuiltCondition :=
    (measurable_armStreamHistoryActionFromWithout hK c n target value).comp
      (measurable_armStreamWithoutCoordinate target)
  have hrebuiltPair : Measurable rebuiltPair :=
    hrebuiltCondition.prodMk (measurable_armStreamCoordinate target)
  have hpairMap :
      Measure.map actualPair ((armStreamMeasure nu).restrict streamBranch) =
        Measure.map rebuiltPair
          ((armStreamMeasure nu).restrict streamBranch) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hstreamBranch] with stream hnext
    change armStreamNextCoordinate hK c n stream = target at hnext
    apply Prod.ext
    · exact armStreamHistoryAction_eq_fromWithout_of_nextCoordinate_eq
        hK c n target value stream hnext
    · change armStreamReward hK c stream (n + 1) =
        armStreamCoordinate target stream
      rw [armStreamReward_succ_eq_nextCoordinate, hnext]
  have hpreimage :
      rebuiltPair ⁻¹' (conditionBranch ×ˢ Set.univ) = streamBranch := by
    ext stream
    change (rebuiltCondition stream ∈ conditionBranch ∧
      armStreamCoordinate target stream ∈ Set.univ) ↔
        stream ∈ streamBranch
    simp only [Set.mem_univ, and_true]
    exact armStreamHistoryActionFromWithout_mem_coordinateBranch_iff
      hK c n target value stream
  calc
    Measure.map actualPair ((armStreamMeasure nu).restrict streamBranch) =
        Measure.map rebuiltPair
          ((armStreamMeasure nu).restrict streamBranch) := hpairMap
    _ = (Measure.map rebuiltPair (armStreamMeasure nu)).restrict
          (conditionBranch ×ˢ Set.univ) := by
      rw [Measure.restrict_map hrebuiltPair
        (hconditionBranch.prod MeasurableSet.univ), hpreimage]
    _ = ((Measure.map rebuiltCondition (armStreamMeasure nu)).prod
          (nu target.2)).restrict (conditionBranch ×ˢ Set.univ) := by
      rw [armStreamMeasure_map_historyActionFromWithout_coordinate_eq_prod
        hK c n nu target value]
    _ = ((Measure.map rebuiltCondition (armStreamMeasure nu)).restrict
          conditionBranch).prod (nu target.2) := by
      rw [Measure.restrict_prod_eq_prod_univ]
    _ = ((Measure.map (armStreamHistoryAction hK c n)
          (armStreamMeasure nu)).restrict conditionBranch).prod
          (nu target.2) := by
      rw [map_historyActionFromWithout_restrict_coordinateBranch_eq_historyAction
        hK c n target value (armStreamMeasure nu)]

/--
The full successor condition/reward joint law is the condition marginal followed
by the stationary law of the arm selected in that condition.
-/
theorem armStreamMeasure_map_historyAction_reward_succ_eq_compProd
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Measure.map
        (fun stream : ArmRewardStream K =>
          (armStreamHistoryAction hK c n stream,
            armStreamReward hK c stream (n + 1)))
        (armStreamMeasure nu) =
      Measure.compProd
        (Measure.map (armStreamHistoryAction hK c n)
          (armStreamMeasure nu))
        (armStreamSelectedRewardKernel n nu) := by
  let actualPair := fun stream : ArmRewardStream K =>
    (armStreamHistoryAction hK c n stream,
      armStreamReward hK c stream (n + 1))
  let conditionMeasure :=
    Measure.map (armStreamHistoryAction hK c n) (armStreamMeasure nu)
  let selectedKernel : Kernel
      (History.FinitePairHistory (Fin K) Real n × Fin K) Real :=
    armStreamSelectedRewardKernel n nu
  have hactualPair : Measurable actualPair :=
    (measurable_armStreamHistoryAction hK c n).prodMk
      (measurable_armStreamReward hK c (n + 1))
  have hstreamPartition :=
    armStreamMeasure_eq_sum_restrict_nextCoordinateBranch hK c n nu
  have hconditionPartition :=
    measure_eq_sum_restrict_armStreamHistoryActionCoordinateBranch
      n conditionMeasure
  have hleft :
      Measure.map actualPair (armStreamMeasure nu) =
        Measure.sum fun target : Nat × Fin K =>
          conditionMeasure.restrict
              (armStreamHistoryActionCoordinateBranch n target) |>.prod
            (nu target.2) := by
    calc
      Measure.map actualPair (armStreamMeasure nu) =
          Measure.map actualPair
            (Measure.sum fun target : Nat × Fin K =>
              (armStreamMeasure nu).restrict
                (armStreamNextCoordinateBranch hK c n target)) := by
        rw [← hstreamPartition]
      _ = Measure.sum fun target : Nat × Fin K =>
          Measure.map actualPair
            ((armStreamMeasure nu).restrict
              (armStreamNextCoordinateBranch hK c n target)) := by
        apply Measure.map_sum
        rw [← hstreamPartition]
        exact hactualPair.aemeasurable
      _ = Measure.sum fun target : Nat × Fin K =>
          conditionMeasure.restrict
              (armStreamHistoryActionCoordinateBranch n target) |>.prod
            (nu target.2) := by
        congr 1
        funext target
        exact armStreamMeasure_map_historyAction_reward_restrict_branch_eq_prod
          hK c n nu target 0
  have hright :
      Measure.compProd conditionMeasure selectedKernel =
        Measure.sum fun target : Nat × Fin K =>
          conditionMeasure.restrict
              (armStreamHistoryActionCoordinateBranch n target) |>.prod
            (nu target.2) := by
    calc
      Measure.compProd conditionMeasure selectedKernel =
          Measure.compProd
            (Measure.sum fun target : Nat × Fin K =>
              conditionMeasure.restrict
                (armStreamHistoryActionCoordinateBranch n target))
            selectedKernel := by
        rw [← hconditionPartition]
      _ = Measure.sum fun target : Nat × Fin K =>
          Measure.compProd
            (conditionMeasure.restrict
              (armStreamHistoryActionCoordinateBranch n target))
            selectedKernel := by
        rw [Measure.compProd_sum_left]
      _ = Measure.sum fun target : Nat × Fin K =>
          conditionMeasure.restrict
              (armStreamHistoryActionCoordinateBranch n target) |>.prod
            (nu target.2) := by
        congr 1
        funext target
        have hselected : Filter.EventuallyEq
            (ae (conditionMeasure.restrict
              (armStreamHistoryActionCoordinateBranch n target)))
            selectedKernel
            (Kernel.const _ (nu target.2)) := by
          filter_upwards [ae_restrict_mem
            (measurableSet_armStreamHistoryActionCoordinateBranch
              n target)] with condition hcondition
          have hsecond : condition.2 = target.2 := by
            simpa [armStreamHistoryActionCoordinateBranch,
              armStreamCoordinateOfHistoryAction] using
                congrArg Prod.snd hcondition
          rw [Kernel.comap_apply, Kernel.const_apply, hsecond]
        rw [Measure.compProd_congr hselected, Measure.compProd_const]
  exact hleft.trans hright.symm

/-- The successor arm-stream reward conditional law is the selected arm law. -/
theorem armStreamReward_succ_condDistrib_ae_eq_nu
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Filter.EventuallyEq
      (ae ((armStreamMeasure nu).map
        (armStreamHistoryAction hK c n)))
      (condDistrib
        (fun stream : ArmRewardStream K =>
          armStreamReward hK c stream (n + 1))
        (armStreamHistoryAction hK c n)
        (armStreamMeasure nu))
      (armStreamSelectedRewardKernel n nu) := by
  refine
    (condDistrib_ae_eq_iff_measure_eq_compProd
      (armStreamHistoryAction hK c n)
      (measurable_armStreamReward hK c (n + 1)).aemeasurable
      (armStreamSelectedRewardKernel n nu)).mpr ?_
  exact armStreamMeasure_map_historyAction_reward_succ_eq_compProd
    hK c n nu

/-- The packaged canonical successor-feedback kernel is the stationary selected law. -/
theorem canonicalArmStreamHistoryEnvironment_feedback_ae_eq_nu
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    Filter.EventuallyEq
      (ae ((armStreamMeasure nu).map
        (armStreamHistoryAction hK (c * (sigma2 : Real)) n)))
      ((canonicalArmStreamHistoryEnvironment hK c sigma2 nu).feedback n)
      (armStreamSelectedRewardKernel n nu) := by
  have hcondition :
      (fun stream : ArmRewardStream K =>
        (History.finitePairHistoryOfTrace
            (armStreamAction hK (c * (sigma2 : Real)) stream)
            (armStreamReward hK (c * (sigma2 : Real)) stream) n,
          armStreamAction hK (c * (sigma2 : Real)) stream (n + 1))) =
        armStreamHistoryAction hK (c * (sigma2 : Real)) n := by
    funext stream
    rw [armStreamAction_succ]
    simp [armStreamHistoryAction,
      armStreamHistory_eq_finitePairHistoryOfTrace]
  simpa only [canonicalArmStreamHistoryEnvironment, hcondition] using
      armStreamReward_succ_condDistrib_ae_eq_nu
        hK (c * (sigma2 : Real)) n nu

/--
Given every other latent coordinate, a fixed coordinate still has its
prescribed stationary arm law.
-/
theorem armStreamMeasure_condDistrib_coordinate_given_without
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (target : Nat × Fin K) :
    Filter.EventuallyEq
      (ae ((armStreamMeasure nu).map
        (armStreamWithoutCoordinate target)))
      (condDistrib (armStreamCoordinate target)
        (armStreamWithoutCoordinate target) (armStreamMeasure nu))
      (Kernel.const _ (nu target.2)) := by
  refine
    (condDistrib_ae_eq_iff_measure_eq_compProd
      (armStreamWithoutCoordinate target)
      (measurable_armStreamCoordinate target).aemeasurable
      (Kernel.const _ (nu target.2))).mpr ?_
  have hjoint :=
    (indepFun_iff_map_prod_eq_prod_map_map
      (measurable_armStreamWithoutCoordinate target).aemeasurable
      (measurable_armStreamCoordinate target).aemeasurable).mp
      (indepFun_armStreamMeasure_coordinate_without nu target).symm
  rw [Measure.compProd_const, hjoint]
  congr 1
  simpa [armStreamCoordinate] using
    armStreamMeasure_map_coord nu target.1 target.2

/-- The initial arm-stream reward conditional law is the selected arm law. -/
theorem armStreamReward_zero_condDistrib_ae_eq_nu
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Filter.EventuallyEq
      (ae ((armStreamMeasure nu).map
        (fun stream : ArmRewardStream K =>
          armStreamAction hK (c * (sigma2 : Real)) stream 0)))
      (condDistrib
        (fun stream : ArmRewardStream K =>
          armStreamReward hK (c * (sigma2 : Real)) stream 0)
        (fun stream : ArmRewardStream K =>
          armStreamAction hK (c * (sigma2 : Real)) stream 0)
        (armStreamMeasure nu))
      nu := by
  let initialArm := initializationArm hK 0
  let condition : ArmRewardStream K -> Fin K := fun _stream => initialArm
  let target : ArmRewardStream K -> Real :=
    armStreamCoordinate (0, initialArm)
  have hcondition : Measurable condition := measurable_const
  have htarget : Measurable target :=
    measurable_armStreamCoordinate (0, initialArm)
  have htarget_map : Measure.map target (armStreamMeasure nu) = nu initialArm := by
    simpa [target, armStreamCoordinate] using
      armStreamMeasure_map_coord nu 0 initialArm
  have hconst : Filter.EventuallyEq
      (ae ((armStreamMeasure nu).map condition))
      (condDistrib target condition (armStreamMeasure nu))
      (Kernel.const _ (nu initialArm)) := by
    refine
      (condDistrib_ae_eq_iff_measure_eq_compProd
        condition htarget.aemeasurable
        (Kernel.const _ (nu initialArm))).mpr ?_
    have hjoint :=
      (indepFun_iff_map_prod_eq_prod_map_map
        hcondition.aemeasurable htarget.aemeasurable).mp
        (indepFun_const_left (μ := armStreamMeasure nu) initialArm target)
    rw [Measure.compProd_const, hjoint, htarget_map]
  have hcondition_map :
      Measure.map condition (armStreamMeasure nu) = Measure.dirac initialArm := by
    simp [condition]
  have hselected : Filter.EventuallyEq
      (ae ((armStreamMeasure nu).map condition))
      (Kernel.const (Fin K) (nu initialArm)) nu := by
    rw [hcondition_map]
    simp only [ae_dirac_eq, Filter.EventuallyEq, Filter.eventually_pure,
      Kernel.const_apply]
  have hresult := hconst.trans hselected
  simpa [condition, target, armStreamCoordinate, armStreamReward,
    rewardFromArmStream] using hresult

/-- The packaged canonical initial-feedback kernel is the stationary selected law. -/
theorem canonicalArmStreamHistoryEnvironment_initialFeedback_ae_eq_nu
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Filter.EventuallyEq
      (ae ((canonicalArmStreamHistoryAlgorithm hK c sigma2 nu).initialAction))
      (canonicalArmStreamHistoryEnvironment hK c sigma2 nu).initialFeedback
      nu := by
  simpa [canonicalArmStreamHistoryAlgorithm,
    canonicalArmStreamHistoryEnvironment] using
    armStreamReward_zero_condDistrib_ae_eq_nu hK c sigma2 nu

end UCB
end BanditRLProof
