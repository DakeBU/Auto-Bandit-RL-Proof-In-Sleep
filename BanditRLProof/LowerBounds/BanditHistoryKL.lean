import BanditRLProof.LowerBounds.ConditionalKernelKL
import BanditRLProof.Algorithms.ThompsonCanonicalTrajectory

/-!
# Same-policy finite-history KL for stochastic bandits

This module connects the conditional-kernel KL integral to the repository's
kernel-valued `HistoryAlgorithm` and canonical Ionescu--Tulcea trajectory.
The observable history includes every sampled action and reward, so the same
possibly randomized nonanticipating policy is shared by both environments.
-/

namespace BanditRLProof
namespace LowerBounds

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u v

/-- The time-zero action/reward pair is measurably equivalent to its singleton history. -/
def pairHistoryZeroMeasurableEquiv
    (Action : Type u) (Reward : Type v)
    [MeasurableSpace Action] [MeasurableSpace Reward] :
    (Action × Reward) ≃ᵐ History.FinitePairHistory Action Reward 0 where
  toEquiv :=
    { toFun := Thompson.singletonPairHistory
      invFun := fun history =>
        history ⟨0, Finset.mem_Iic.mpr le_rfl⟩
      left_inv := fun _pair => rfl
      right_inv := fun history => by
        funext index
        have hindex : index = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ :=
          Subsingleton.elim _ _
        subst index
        rfl }
  measurable_toFun := Thompson.measurable_singletonPairHistory
  measurable_invFun := measurable_pi_apply _

/-- A finite history and one next pair are measurably equivalent to the successor history. -/
def pairHistorySuccMeasurableEquiv
    (Action : Type u) (Reward : Type v)
    [MeasurableSpace Action] [MeasurableSpace Reward] (n : Nat) :
    (History.FinitePairHistory Action Reward n × (Action × Reward)) ≃ᵐ
      History.FinitePairHistory Action Reward (n + 1) :=
  (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl
        (History.FinitePairHistory Action Reward n))
      (MeasurableEquiv.piSingleton
        (X := fun _ : Nat => Action × Reward) n)).trans
    (MeasurableEquiv.IicProdIoc
      (X := fun _ : Nat => Action × Reward) (Nat.le_succ n))

theorem pairHistoryZeroMeasurableEquiv_apply
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (pair : Action × Reward) :
    pairHistoryZeroMeasurableEquiv Action Reward pair =
      Thompson.singletonPairHistory pair := by
  funext index
  have hindex : index = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := Subsingleton.elim _ _
  subst index
  rfl

theorem pairHistorySuccMeasurableEquiv_apply
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (n : Nat)
    (input : History.FinitePairHistory Action Reward n × (Action × Reward)) :
    pairHistorySuccMeasurableEquiv Action Reward n input =
      History.extendPairHistorySucc input.1 input.2 := by
  funext index
  by_cases hindex : index.1 ≤ n
  · simp [pairHistorySuccMeasurableEquiv, MeasurableEquiv.IicProdIoc,
      MeasurableEquiv.piSingleton, MeasurableEquiv.prodCongr,
      Equiv.prodCongr, MeasurableEquiv.refl,
      History.extendPairHistorySucc, hindex]
  · have hle : index.1 ≤ n + 1 := Finset.mem_Iic.mp index.2
    have hsucc : index.1 = n + 1 := by
      omega
    simp [pairHistorySuccMeasurableEquiv, MeasurableEquiv.IicProdIoc,
      MeasurableEquiv.piSingleton, MeasurableEquiv.prodCongr,
      Equiv.prodCongr, MeasurableEquiv.refl,
      History.extendPairHistorySucc, hsucc]

/-- A stationary arm-indexed reward kernel viewed as a history environment. -/
noncomputable def stationaryBanditHistoryEnvironment
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw] :
    Thompson.HistoryEnvironment (Fin K) Reward where
  initialFeedback := armLaw
  feedback _ := armLaw.comap Prod.snd measurable_snd

@[simp]
theorem stationaryBanditHistoryEnvironment_initialFeedback
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw] :
    (stationaryBanditHistoryEnvironment armLaw).initialFeedback = armLaw := rfl

@[simp]
theorem stationaryBanditHistoryEnvironment_feedback_apply
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (n : Nat) (history : History.FinitePairHistory (Fin K) Reward n)
    (arm : Fin K) :
    (stationaryBanditHistoryEnvironment armLaw).feedback n (history, arm) =
      armLaw arm := by
  rw [stationaryBanditHistoryEnvironment, Kernel.comap_apply]

/-- Law of the observable action/reward history through the inclusive round `n`. -/
noncomputable def canonicalBanditHistoryMeasure
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (n : Nat) : Measure (History.FinitePairHistory (Fin K) Reward n) :=
  (Thompson.canonicalHistoryTrajectoryMeasure algorithm
    (stationaryBanditHistoryEnvironment armLaw)).map
      (Preorder.frestrictLe n)

instance instCanonicalBanditHistoryMeasureIsProbability
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (n : Nat) :
    IsProbabilityMeasure
      (canonicalBanditHistoryMeasure algorithm armLaw n) := by
  unfold canonicalBanditHistoryMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The inclusive time-zero history is the initial action/reward law in singleton form. -/
theorem canonicalBanditHistoryMeasure_zero
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw] :
    canonicalBanditHistoryMeasure algorithm armLaw 0 =
      (algorithm.initialAction ⊗ₘ armLaw).map
        (pairHistoryZeroMeasurableEquiv (Fin K) Reward) := by
  let trajectoryMeasure :=
    Thompson.canonicalHistoryTrajectoryMeasure algorithm
      (stationaryBanditHistoryEnvironment armLaw)
  have hprefix :
      (Preorder.frestrictLe 0 :
          ((n : Nat) → Fin K × Reward) →
            History.FinitePairHistory (Fin K) Reward 0) =
        fun trajectory =>
          pairHistoryZeroMeasurableEquiv (Fin K) Reward (trajectory 0) := by
    funext trajectory index
    have hindex : index = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ :=
      Subsingleton.elim _ _
    subst index
    rfl
  have hinitial :
      trajectoryMeasure.map (fun trajectory => trajectory 0) =
        algorithm.initialAction ⊗ₘ armLaw := by
    simpa [trajectoryMeasure, Thompson.canonicalHistoryTrajectoryAction,
      Thompson.canonicalHistoryTrajectoryReward] using
      (Thompson.canonicalHistoryTrajectory_initialPair_map_eq algorithm
        (stationaryBanditHistoryEnvironment armLaw))
  change trajectoryMeasure.map (Preorder.frestrictLe 0) = _
  rw [hprefix]
  change trajectoryMeasure.map
      ((pairHistoryZeroMeasurableEquiv (Fin K) Reward) ∘
        fun trajectory => trajectory 0) = _
  rw [← Measure.map_map
    (pairHistoryZeroMeasurableEquiv (Fin K) Reward).measurable
    (measurable_pi_apply 0), hinitial]

/--
The inclusive successor history is obtained from the prefix history and the
canonical same-policy action/reward step, then re-encoded by a measurable
equivalence.
-/
theorem canonicalBanditHistoryMeasure_succ
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (n : Nat) :
    canonicalBanditHistoryMeasure algorithm armLaw (n + 1) =
      (canonicalBanditHistoryMeasure algorithm armLaw n ⊗ₘ
          Thompson.historyStepKernel algorithm
            (stationaryBanditHistoryEnvironment armLaw) n).map
        (pairHistorySuccMeasurableEquiv (Fin K) Reward n) := by
  let trajectoryMeasure :=
    Thompson.canonicalHistoryTrajectoryMeasure algorithm
      (stationaryBanditHistoryEnvironment armLaw)
  let stepKernel := fun m =>
    Thompson.historyStepKernel algorithm
      (stationaryBanditHistoryEnvironment armLaw) m
  have hjoint :
      trajectoryMeasure.map (Preorder.frestrictLe n) ⊗ₘ stepKernel n =
        trajectoryMeasure.map (fun trajectory =>
          (Preorder.frestrictLe n trajectory, trajectory (n + 1))) := by
    simpa [trajectoryMeasure, stepKernel,
      Thompson.canonicalHistoryTrajectoryMeasure] using
      (ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
          (X := fun _ : Nat => Fin K × Reward)
          (μ₀ := algorithm.initialAction ⊗ₘ armLaw)
          (κ := stepKernel) (a := n))
  have hencode :
      (Preorder.frestrictLe (n + 1) :
          ((m : Nat) → Fin K × Reward) →
            History.FinitePairHistory (Fin K) Reward (n + 1)) =
        fun trajectory =>
          pairHistorySuccMeasurableEquiv (Fin K) Reward n
            (Preorder.frestrictLe n trajectory, trajectory (n + 1)) := by
    funext trajectory
    rw [pairHistorySuccMeasurableEquiv_apply]
    funext index
    by_cases hindex : index.1 ≤ n
    · simp [History.extendPairHistorySucc, hindex]
    · have hle : index.1 ≤ n + 1 := Finset.mem_Iic.mp index.2
      have hsucc : index.1 = n + 1 := by omega
      simp [History.extendPairHistorySucc, hsucc]
  change trajectoryMeasure.map (Preorder.frestrictLe (n + 1)) = _
  rw [hencode]
  change trajectoryMeasure.map
      ((pairHistorySuccMeasurableEquiv (Fin K) Reward n) ∘
        fun trajectory =>
          (Preorder.frestrictLe n trajectory, trajectory (n + 1))) = _
  rw [← Measure.map_map
    (pairHistorySuccMeasurableEquiv (Fin K) Reward n).measurable
    ((Preorder.measurable_frestrictLe n).prodMk
      (measurable_pi_apply (n + 1)))]
  rw [← hjoint]
  rfl

/--
At the first pull, same-policy history KL is the initial-action average of the
arm-law KL divergence.  The expectation is under the first environment.
-/
theorem klDiv_canonicalBanditHistoryMeasure_zero
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (h_ac : ∀ arm, armLaw arm ≪ referenceArmLaw arm) :
    InformationTheory.klDiv
        (canonicalBanditHistoryMeasure algorithm armLaw 0)
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw 0) =
      ∫⁻ arm, InformationTheory.klDiv
        (armLaw arm) (referenceArmLaw arm) ∂algorithm.initialAction := by
  rw [canonicalBanditHistoryMeasure_zero algorithm armLaw,
    canonicalBanditHistoryMeasure_zero algorithm referenceArmLaw]
  rw [klDiv_map_measurableEquiv]
  exact klDiv_compProd_same_left_eq_lintegral_klDiv
    algorithm.initialAction armLaw referenceArmLaw h_ac

/--
One successor round adds the first-environment policy average of the selected
arm KL divergence.  This is the exact adaptive-history chain-rule step; the
possibly randomized policy is shared and contributes no additional KL term.
-/
theorem klDiv_canonicalBanditHistoryMeasure_succ
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (h_ac : ∀ arm, armLaw arm ≪ referenceArmLaw arm)
    (n : Nat) :
    InformationTheory.klDiv
        (canonicalBanditHistoryMeasure algorithm armLaw (n + 1))
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw (n + 1)) =
      InformationTheory.klDiv
          (canonicalBanditHistoryMeasure algorithm armLaw n)
          (canonicalBanditHistoryMeasure algorithm referenceArmLaw n) +
        ∫⁻ history, ∫⁻ arm,
          InformationTheory.klDiv
            (armLaw arm) (referenceArmLaw arm)
            ∂algorithm.policy n history
          ∂canonicalBanditHistoryMeasure algorithm armLaw n := by
  rw [canonicalBanditHistoryMeasure_succ algorithm armLaw n,
    canonicalBanditHistoryMeasure_succ algorithm referenceArmLaw n]
  rw [klDiv_map_measurableEquiv]
  rw [InformationTheory.klDiv_compProd_eq_add]
  congr 1
  simpa [Thompson.historyStepKernel,
    stationaryBanditHistoryEnvironment] using
    (klDiv_historyStep_samePolicy_eq_iterated_lintegral_armKL
      (canonicalBanditHistoryMeasure algorithm armLaw n)
      (algorithm.policy n) armLaw referenceArmLaw h_ac)

/-- First-environment probability mass assigned to one arm at successor round `n + 1`. -/
noncomputable def canonicalPolicyArmMass
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (n : Nat) (arm : Fin K) : ENNReal :=
  ∫⁻ history,
    algorithm.policy n history ({arm} : Set (Fin K))
    ∂canonicalBanditHistoryMeasure algorithm armLaw n

/--
Expected number of selections of `arm` through inclusive round `n`: the
initial-action mass plus the successor policy masses for rounds `1, ..., n`.
The equality with the lower integral of the realized finite-history pull count
is proved below; this definition exposes the recurrence used by the KL proof.
-/
noncomputable def canonicalExpectedPullCountThrough
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (n : Nat) (arm : Fin K) : ENNReal :=
  algorithm.initialAction ({arm} : Set (Fin K)) +
    ∑ round ∈ Finset.range n,
      canonicalPolicyArmMass algorithm armLaw round arm

@[simp]
theorem canonicalExpectedPullCountThrough_zero
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (arm : Fin K) :
    canonicalExpectedPullCountThrough algorithm armLaw 0 arm =
      algorithm.initialAction ({arm} : Set (Fin K)) := by
  simp [canonicalExpectedPullCountThrough]

theorem canonicalExpectedPullCountThrough_succ
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (n : Nat) (arm : Fin K) :
    canonicalExpectedPullCountThrough algorithm armLaw (n + 1) arm =
      canonicalExpectedPullCountThrough algorithm armLaw n arm +
        canonicalPolicyArmMass algorithm armLaw n arm := by
  simp [canonicalExpectedPullCountThrough, Finset.sum_range_succ,
    add_assoc]

/-- A finite-action conditional cost integral regroups by action mass. -/
theorem lintegral_lintegral_fin_eq_sum_armMass_mul
    {K : Nat} {History : Type*}
    [MeasurableSpace History]
    (historyLaw : Measure History)
    (policy : Kernel History (Fin K)) [IsMarkovKernel policy]
    (cost : Fin K → ENNReal) :
    (∫⁻ history, ∫⁻ arm, cost arm ∂policy history ∂historyLaw) =
      ∑ arm : Fin K,
        (∫⁻ history,
          policy history ({arm} : Set (Fin K)) ∂historyLaw) * cost arm := by
  classical
  simp_rw [MeasureTheory.lintegral_fintype]
  rw [MeasureTheory.lintegral_finset_sum]
  · apply Finset.sum_congr rfl
    intro arm _harm
    rw [MeasureTheory.lintegral_const_mul _
      (policy.measurable_coe (MeasurableSet.singleton arm))]
    rw [mul_comm]
  · intro arm _harm
    exact measurable_const.mul
      (policy.measurable_coe (MeasurableSet.singleton arm))

/-- Policy-mass recurrence form of the finite-history KL decomposition. -/
theorem klDiv_canonicalBanditHistoryMeasure_eq_sum_expectedPullCount_mul_armKL
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (h_ac : ∀ arm, armLaw arm ≪ referenceArmLaw arm)
    (n : Nat) :
    InformationTheory.klDiv
        (canonicalBanditHistoryMeasure algorithm armLaw n)
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw n) =
      ∑ arm : Fin K,
        canonicalExpectedPullCountThrough algorithm armLaw n arm *
          InformationTheory.klDiv
            (armLaw arm) (referenceArmLaw arm) := by
  induction n with
  | zero =>
      rw [klDiv_canonicalBanditHistoryMeasure_zero
        algorithm armLaw referenceArmLaw h_ac]
      rw [MeasureTheory.lintegral_fintype]
      apply Finset.sum_congr rfl
      intro arm _harm
      simp [mul_comm]
  | succ n ih =>
      rw [klDiv_canonicalBanditHistoryMeasure_succ
        algorithm armLaw referenceArmLaw h_ac n, ih]
      rw [lintegral_lintegral_fin_eq_sum_armMass_mul]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro arm _harm
      rw [canonicalExpectedPullCountThrough_succ]
      simp only [canonicalPolicyArmMass, add_mul]

/-- Realized pull count encoded directly on an inclusive finite history. -/
noncomputable def finiteHistoryPullCountENNReal
    {K : Nat} {Reward : Type v} :
    (n : Nat) → History.FinitePairHistory (Fin K) Reward n → Fin K → ENNReal
  | 0, history, arm =>
      if (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1 = arm then 1 else 0
  | n + 1, history, arm =>
      finiteHistoryPullCountENNReal n (Thompson.pairHistoryPrefix history) arm +
        if (Thompson.pairHistoryLast history).1 = arm then 1 else 0

theorem measurable_finiteHistoryPullCountENNReal
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (n : Nat) (arm : Fin K) :
    Measurable (fun history : History.FinitePairHistory (Fin K) Reward n =>
      finiteHistoryPullCountENNReal n history arm) := by
  induction n with
  | zero =>
      exact Measurable.ite
        (measurableSet_eq_fun
          (measurable_fst.comp (measurable_pi_apply _)) measurable_const)
        measurable_const measurable_const
  | succ n ih =>
      exact (ih.comp Thompson.measurable_pairHistoryPrefix).add
        (Measurable.ite
          (measurableSet_eq_fun
            (measurable_fst.comp Thompson.measurable_pairHistoryLast)
            measurable_const)
          measurable_const measurable_const)

@[simp]
theorem finiteHistoryPullCountENNReal_pairHistoryZeroMeasurableEquiv
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (pair : Fin K × Reward) (arm : Fin K) :
    finiteHistoryPullCountENNReal 0
        (pairHistoryZeroMeasurableEquiv (Fin K) Reward pair) arm =
      if pair.1 = arm then 1 else 0 := by
  rw [pairHistoryZeroMeasurableEquiv_apply]
  change (if pair.1 = arm then 1 else 0) = _
  rfl

@[simp]
theorem finiteHistoryPullCountENNReal_pairHistorySuccMeasurableEquiv
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (n : Nat)
    (input : History.FinitePairHistory (Fin K) Reward n × (Fin K × Reward))
    (arm : Fin K) :
    finiteHistoryPullCountENNReal (n + 1)
        (pairHistorySuccMeasurableEquiv (Fin K) Reward n input) arm =
      finiteHistoryPullCountENNReal n input.1 arm +
        if input.2.1 = arm then 1 else 0 := by
  rw [pairHistorySuccMeasurableEquiv_apply]
  simp [finiteHistoryPullCountENNReal]

/-- Lower integral of the realized pull count on the generated finite history. -/
noncomputable def canonicalRealizedExpectedPullCountThrough
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (n : Nat) (arm : Fin K) : ENNReal :=
  ∫⁻ history,
    finiteHistoryPullCountENNReal n history arm
    ∂canonicalBanditHistoryMeasure algorithm armLaw n

/-- The action indicator under a history-step kernel integrates to policy mass. -/
theorem lintegral_historyStepKernel_armIndicator_eq_policy_mass
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (environment : Thompson.HistoryEnvironment (Fin K) Reward)
    (n : Nat)
    (history : History.FinitePairHistory (Fin K) Reward n)
    (arm : Fin K) :
    (∫⁻ pair,
        ({arm} : Set (Fin K)).indicator (fun _ => (1 : ENNReal)) pair.1
        ∂Thompson.historyStepKernel algorithm environment n history) =
      algorithm.policy n history ({arm} : Set (Fin K)) := by
  calc
    (∫⁻ pair,
        ({arm} : Set (Fin K)).indicator (fun _ => (1 : ENNReal)) pair.1
        ∂Thompson.historyStepKernel algorithm environment n history) =
        ∫⁻ selectedArm,
          ({arm} : Set (Fin K)).indicator (fun _ => (1 : ENNReal)) selectedArm
          ∂(Thompson.historyStepKernel algorithm environment n history).map
            Prod.fst := by
      rw [MeasureTheory.lintegral_map
        (measurable_const.indicator (MeasurableSet.singleton arm)) measurable_fst]
    _ = ∫⁻ selectedArm,
          ({arm} : Set (Fin K)).indicator (fun _ => (1 : ENNReal)) selectedArm
          ∂algorithm.policy n history := by
      have hmap :
          (Thompson.historyStepKernel algorithm environment n history).map
              Prod.fst =
            algorithm.policy n history := by
        rw [← ProbabilityTheory.Kernel.map_apply _ measurable_fst,
          Thompson.historyStepKernel_map_fst]
      rw [hmap]
    _ = algorithm.policy n history ({arm} : Set (Fin K)) := by
      rw [MeasureTheory.lintegral_indicator (MeasurableSet.singleton arm)]
      exact MeasureTheory.setLIntegral_one _

@[simp]
theorem canonicalRealizedExpectedPullCountThrough_zero
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (arm : Fin K) :
    canonicalRealizedExpectedPullCountThrough algorithm armLaw 0 arm =
      algorithm.initialAction ({arm} : Set (Fin K)) := by
  classical
  unfold canonicalRealizedExpectedPullCountThrough
  rw [canonicalBanditHistoryMeasure_zero algorithm armLaw]
  rw [MeasureTheory.lintegral_map_equiv]
  simp_rw [finiteHistoryPullCountENNReal_pairHistoryZeroMeasurableEquiv]
  have hindicator :
      (fun pair : Fin K × Reward =>
          if pair.1 = arm then (1 : ENNReal) else 0) =
        fun pair =>
          ({arm} : Set (Fin K)).indicator (fun _ => (1 : ENNReal)) pair.1 := by
    funext pair
    simp [Set.indicator, eq_comm]
  rw [hindicator]
  rw [MeasureTheory.lintegral_indicator_const_comp measurable_fst
    (MeasurableSet.singleton arm)]
  simp only [one_mul]
  calc
    (algorithm.initialAction ⊗ₘ armLaw)
        (Prod.fst ⁻¹' ({arm} : Set (Fin K))) =
        (algorithm.initialAction ⊗ₘ armLaw).fst
          ({arm} : Set (Fin K)) := by
      rw [Measure.fst_apply (MeasurableSet.singleton arm)]
    _ = algorithm.initialAction ({arm} : Set (Fin K)) := by
      rw [Measure.fst_compProd]

theorem canonicalRealizedExpectedPullCountThrough_succ
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (n : Nat) (arm : Fin K) :
    canonicalRealizedExpectedPullCountThrough algorithm armLaw (n + 1) arm =
      canonicalRealizedExpectedPullCountThrough algorithm armLaw n arm +
        canonicalPolicyArmMass algorithm armLaw n arm := by
  classical
  unfold canonicalRealizedExpectedPullCountThrough
  rw [canonicalBanditHistoryMeasure_succ algorithm armLaw n]
  rw [MeasureTheory.lintegral_map_equiv]
  simp_rw [finiteHistoryPullCountENNReal_pairHistorySuccMeasurableEquiv]
  let historyLaw := canonicalBanditHistoryMeasure algorithm armLaw n
  let stepKernel := Thompson.historyStepKernel algorithm
    (stationaryBanditHistoryEnvironment armLaw) n
  have hcountMeasurable :
      Measurable (fun input :
          History.FinitePairHistory (Fin K) Reward n × (Fin K × Reward) =>
        finiteHistoryPullCountENNReal n input.1 arm) :=
    (measurable_finiteHistoryPullCountENNReal n arm).comp measurable_fst
  rw [MeasureTheory.lintegral_add_left hcountMeasurable]
  congr 1
  · change (∫⁻ input,
        finiteHistoryPullCountENNReal n input.1 arm
        ∂historyLaw ⊗ₘ stepKernel) = _
    rw [Measure.lintegral_compProd hcountMeasurable]
    simp
    rfl
  · have hindicator :
        (fun input :
            History.FinitePairHistory (Fin K) Reward n × (Fin K × Reward) =>
          if input.2.1 = arm then (1 : ENNReal) else 0) =
          fun input =>
            ({arm} : Set (Fin K)).indicator (fun _ => (1 : ENNReal))
              input.2.1 := by
        funext input
        simp [Set.indicator, eq_comm]
    rw [hindicator]
    have hindicatorMeasurable :
        Measurable (fun input :
            History.FinitePairHistory (Fin K) Reward n × (Fin K × Reward) =>
          ({arm} : Set (Fin K)).indicator (fun _ => (1 : ENNReal))
            input.2.1) :=
      (measurable_const.indicator (MeasurableSet.singleton arm)).comp
        (measurable_fst.comp measurable_snd)
    change (∫⁻ input,
        ({arm} : Set (Fin K)).indicator (fun _ => (1 : ENNReal))
          input.2.1 ∂historyLaw ⊗ₘ stepKernel) = _
    rw [Measure.lintegral_compProd hindicatorMeasurable]
    simp_rw [stepKernel,
      lintegral_historyStepKernel_armIndicator_eq_policy_mass]
    rfl

/--
The policy-mass recurrence is exactly the lower integral of the realized pull
count on the first-environment finite history.
-/
theorem canonicalRealizedExpectedPullCountThrough_eq_expectedPullCountThrough
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (n : Nat) (arm : Fin K) :
    canonicalRealizedExpectedPullCountThrough algorithm armLaw n arm =
      canonicalExpectedPullCountThrough algorithm armLaw n arm := by
  induction n with
  | zero =>
      rw [canonicalRealizedExpectedPullCountThrough_zero,
        canonicalExpectedPullCountThrough_zero]
  | succ n ih =>
      rw [canonicalRealizedExpectedPullCountThrough_succ,
        canonicalExpectedPullCountThrough_succ, ih]

/-- The first-pull KL identity, including singular and infinite-divergence arms. -/
theorem klDiv_canonicalBanditHistoryMeasure_zero_general
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw] :
    InformationTheory.klDiv
        (canonicalBanditHistoryMeasure algorithm armLaw 0)
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw 0) =
      ∫⁻ arm, InformationTheory.klDiv
        (armLaw arm) (referenceArmLaw arm) ∂algorithm.initialAction := by
  rw [canonicalBanditHistoryMeasure_zero algorithm armLaw,
    canonicalBanditHistoryMeasure_zero algorithm referenceArmLaw]
  rw [klDiv_map_measurableEquiv]
  exact klDiv_finiteAction_compProd_eq_lintegral_armKL
    algorithm.initialAction armLaw referenceArmLaw

/-- General successor KL recursion for a common randomized history policy. -/
theorem klDiv_canonicalBanditHistoryMeasure_succ_general
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (n : Nat) :
    InformationTheory.klDiv
        (canonicalBanditHistoryMeasure algorithm armLaw (n + 1))
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw (n + 1)) =
      InformationTheory.klDiv
          (canonicalBanditHistoryMeasure algorithm armLaw n)
          (canonicalBanditHistoryMeasure algorithm referenceArmLaw n) +
        ∫⁻ history, ∫⁻ arm,
          InformationTheory.klDiv
            (armLaw arm) (referenceArmLaw arm)
            ∂algorithm.policy n history
          ∂canonicalBanditHistoryMeasure algorithm armLaw n := by
  rw [canonicalBanditHistoryMeasure_succ algorithm armLaw n,
    canonicalBanditHistoryMeasure_succ algorithm referenceArmLaw n]
  rw [klDiv_map_measurableEquiv]
  rw [InformationTheory.klDiv_compProd_eq_add]
  congr 1
  simpa [Thompson.historyStepKernel,
    stationaryBanditHistoryEnvironment] using
    (klDiv_historyStep_samePolicy_eq_iterated_lintegral_armKL_general
      (canonicalBanditHistoryMeasure algorithm armLaw n)
      (algorithm.policy n) armLaw referenceArmLaw)

/-- Policy-mass form of the unrestricted finite-history decomposition. -/
theorem klDiv_canonicalBanditHistoryMeasure_eq_sum_expectedPullCount_mul_armKL_general
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (n : Nat) :
    InformationTheory.klDiv
        (canonicalBanditHistoryMeasure algorithm armLaw n)
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw n) =
      ∑ arm : Fin K,
        canonicalExpectedPullCountThrough algorithm armLaw n arm *
          InformationTheory.klDiv
            (armLaw arm) (referenceArmLaw arm) := by
  induction n with
  | zero =>
      rw [klDiv_canonicalBanditHistoryMeasure_zero_general
        algorithm armLaw referenceArmLaw]
      rw [MeasureTheory.lintegral_fintype]
      apply Finset.sum_congr rfl
      intro arm _harm
      simp [mul_comm]
  | succ n ih =>
      rw [klDiv_canonicalBanditHistoryMeasure_succ_general
        algorithm armLaw referenceArmLaw n, ih]
      rw [lintegral_lintegral_fin_eq_sum_armMass_mul]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro arm _harm
      rw [canonicalExpectedPullCountThrough_succ]
      simp only [canonicalPolicyArmMass, add_mul]

/--
Lattimore--Szepesvari Lemma 15.1 in the repository's inclusive-round
convention.  `canonicalBanditHistoryMeasure ... n` contains exactly `n + 1`
action/reward pairs. Its directed KL divergence is the finite-arm sum of the
first-environment lower integrals of the realized pull counts through round
`n`, multiplied by the arm-law KL divergences. The algorithm is one common,
possibly randomized, nonanticipating history policy in both environments.
-/
theorem klDiv_canonicalBanditHistoryMeasure_eq_sum_realizedExpectedPullCount_mul_armKL
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (n : Nat) :
    InformationTheory.klDiv
        (canonicalBanditHistoryMeasure algorithm armLaw n)
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw n) =
      ∑ arm : Fin K,
        canonicalRealizedExpectedPullCountThrough algorithm armLaw n arm *
          InformationTheory.klDiv
            (armLaw arm) (referenceArmLaw arm) := by
  rw [klDiv_canonicalBanditHistoryMeasure_eq_sum_expectedPullCount_mul_armKL_general
    algorithm armLaw referenceArmLaw n]
  apply Finset.sum_congr rfl
  intro arm _harm
  rw [canonicalRealizedExpectedPullCountThrough_eq_expectedPullCountThrough]

/--
Source-facing name for Lattimore--Szepesvari Lemma 15.1 / Eq. (15.1).
The local history index `lastRound` represents exactly `lastRound + 1` pulls.
-/
theorem banditHistoryRelativeEntropy_eq_expectedPulls_sum
    {K : Nat} {Reward : Type v}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (lastRound : Nat) :
    InformationTheory.klDiv
        (canonicalBanditHistoryMeasure algorithm armLaw lastRound)
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound) =
      ∑ arm : Fin K,
        canonicalRealizedExpectedPullCountThrough
            algorithm armLaw lastRound arm *
          InformationTheory.klDiv
            (armLaw arm) (referenceArmLaw arm) :=
  klDiv_canonicalBanditHistoryMeasure_eq_sum_realizedExpectedPullCount_mul_armKL
    algorithm armLaw referenceArmLaw lastRound

end

end LowerBounds
end BanditRLProof
