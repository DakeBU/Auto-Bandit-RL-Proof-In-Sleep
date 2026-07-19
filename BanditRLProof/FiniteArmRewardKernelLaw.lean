import BanditRLProof.BoundedRewardKernelLaw

/-!
# Context-independent finite-arm centered reward laws

This module packages action-indexed probability laws into the centered reward
kernel contract shared by bandit algorithms. It is deliberately independent
of ETC, UCB, or any trajectory construction.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory

namespace Concentration

/-- The largest Hoeffding proxy among a finite family of armwise intervals. -/
noncomputable def finiteArmIntervalVarianceProxy
    {K : Nat} (lo hi : Fin K -> Real) : NNReal :=
  Finset.univ.sup fun arm => intervalVarianceProxy (lo arm) (hi arm)

/-- Every armwise interval proxy is bounded by the finite-arm maximum proxy. -/
theorem intervalVarianceProxy_le_finiteArmIntervalVarianceProxy
    {K : Nat} (lo hi : Fin K -> Real) (arm : Fin K) :
    intervalVarianceProxy (lo arm) (hi arm) <=
      finiteArmIntervalVarianceProxy lo hi := by
  change intervalVarianceProxy (lo arm) (hi arm) <=
    (Finset.univ : Finset (Fin K)).sup
      (fun arm => intervalVarianceProxy (lo arm) (hi arm))
  exact Finset.le_sup
    (s := (Finset.univ : Finset (Fin K)))
    (f := fun arm => intervalVarianceProxy (lo arm) (hi arm))
    (Finset.mem_univ arm)

/-- Nondegenerate armwise intervals give a positive finite-arm maximum proxy. -/
theorem finiteArmIntervalVarianceProxy_pos
    {K : Nat} (hK : 0 < K) (lo hi : Fin K -> Real)
    (hlohi : forall arm, lo arm < hi arm) :
    0 < ((finiteArmIntervalVarianceProxy lo hi : NNReal) : Real) := by
  let arm : Fin K := Fin.mk 0 hK
  have harmPos :
      0 < ((intervalVarianceProxy (lo arm) (hi arm) : NNReal) : Real) :=
    intervalVarianceProxy_pos_of_lt (hlohi arm)
  have harmLe :
      intervalVarianceProxy (lo arm) (hi arm) <=
        finiteArmIntervalVarianceProxy lo hi :=
    intervalVarianceProxy_le_finiteArmIntervalVarianceProxy lo hi arm
  exact harmPos.trans_le (by exact_mod_cast harmLe)

end Concentration

namespace Concentration

/-- The largest variance proxy in a finite family of arms. -/
noncomputable def finiteArmVarianceProxy
    {K : Nat} (varianceProxy : Fin K -> NNReal) : NNReal :=
  Finset.univ.sup varianceProxy

/-- Every arm proxy is bounded by the finite-arm maximum proxy. -/
theorem varianceProxy_le_finiteArmVarianceProxy
    {K : Nat} (varianceProxy : Fin K -> NNReal) (arm : Fin K) :
    varianceProxy arm <= finiteArmVarianceProxy varianceProxy := by
  change varianceProxy arm <=
    (Finset.univ : Finset (Fin K)).sup varianceProxy
  exact Finset.le_sup
    (s := (Finset.univ : Finset (Fin K)))
    (f := varianceProxy)
    (Finset.mem_univ arm)

/-- A positive member makes the finite-arm maximum proxy positive. -/
theorem finiteArmVarianceProxy_pos_of_exists
    {K : Nat} (varianceProxy : Fin K -> NNReal)
    (hpos : exists arm, 0 < ((varianceProxy arm : NNReal) : Real)) :
    0 < ((finiteArmVarianceProxy varianceProxy : NNReal) : Real) := by
  rcases hpos with ⟨arm, harm⟩
  have hle : varianceProxy arm <= finiteArmVarianceProxy varianceProxy :=
    varianceProxy_le_finiteArmVarianceProxy varianceProxy arm
  exact harm.trans_le (by exact_mod_cast hle)

end Concentration

namespace RewardKernel

/--
Action-indexed probability laws with exact means and direct centered
sub-Gaussian witnesses form a context-independent centered reward-kernel law.
-/
noncomputable def
    contextIndependentCenteredRewardKernelLaw_of_hasSubgaussianMGF
    {Context Action : Type}
    [MeasurableSpace Context] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [Countable Action]
    (armLaw : Action -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (armMean : Action -> Rat)
    (varianceProxy : Action -> NNReal)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((armMean arm : Rat) : Real))
    (hsubG : forall arm,
      HasSubgaussianMGF
        (fun reward : Rat => (((reward - armMean arm : Rat) : Real)))
        (varianceProxy arm) (armLaw arm)) :
    CenteredRewardKernelLaw
      (contextIndependentOfActionLaws
        (Context := Context) armLaw hprob)
      (fun _ arm => armMean arm)
      (fun _ arm => varianceProxy arm) where
  integrable := by
    intro context arm
    rw [selectedMeasure_contextIndependentOfActionLaws]
    exact (hsubG arm).integrable
  integral_eq_zero := by
    intro context arm
    haveI : IsProbabilityMeasure (armLaw arm) := hprob arm
    have hcenter := (hsubG arm).integrable
    have hconst : Integrable
        (fun _reward : Rat => ((armMean arm : Rat) : Real))
        (armLaw arm) := integrable_const _
    have hraw : Integrable
        (fun reward : Rat => ((reward : Rat) : Real)) (armLaw arm) := by
      convert hcenter.add hconst using 1
      funext reward
      simp
    rw [selectedMeasure_contextIndependentOfActionLaws]
    simp_rw [Rat.cast_sub]
    rw [integral_sub hraw hconst, hmean arm]
    simp
  hasSubgaussianMGF := by
    intro context arm
    rw [selectedMeasure_contextIndependentOfActionLaws]
    exact hsubG arm

/--
Common almost-sure interval bounds and exact means form a
context-independent centered reward-kernel law with the Hoeffding proxy.
-/
noncomputable def contextIndependentBoundedCenteredRewardKernelLaw
    {Context Action : Type}
    [MeasurableSpace Context] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [Countable Action]
    (armLaw : Action -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (armMean : Action -> Rat)
    (lo hi : Real)
    (hmeas : forall arm,
      AEMeasurable (fun reward : Rat => ((reward : Rat) : Real))
        (armLaw arm))
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Rat => Set.Icc lo hi ((reward : Rat) : Real))
        (ae (armLaw arm)))
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((armMean arm : Rat) : Real)) :
    CenteredRewardKernelLaw
      (contextIndependentOfActionLaws
        (Context := Context) armLaw hprob)
      (fun _ arm => armMean arm)
      (fun _ _ => Concentration.intervalVarianceProxy lo hi) := by
  apply contextIndependentCenteredRewardKernelLaw_of_hasSubgaussianMGF
    armLaw hprob armMean
      (fun _ => Concentration.intervalVarianceProxy lo hi) hmean
  intro arm
  haveI : IsProbabilityMeasure (armLaw arm) := hprob arm
  simpa [Rat.cast_sub] using
    (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
      (mu := armLaw arm)
      (X := fun reward : Rat => ((reward : Rat) : Real))
      (lo := lo)
      (hi := hi)
      (mean := ((armMean arm : Rat) : Real))
      (hmeas arm) (hbound arm) (hmean arm))

/--
Arm-dependent almost-sure interval bounds and exact means form a
context-independent centered reward-kernel law with armwise Hoeffding proxies.
-/
noncomputable def contextIndependentArmwiseBoundedCenteredRewardKernelLaw
    {Context Action : Type}
    [MeasurableSpace Context] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [Countable Action]
    (armLaw : Action -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (armMean : Action -> Rat)
    (lo hi : Action -> Real)
    (hmeas : forall arm,
      AEMeasurable (fun reward : Rat => ((reward : Rat) : Real))
        (armLaw arm))
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Rat => Set.Icc (lo arm) (hi arm)
          ((reward : Rat) : Real))
        (ae (armLaw arm)))
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((armMean arm : Rat) : Real)) :
    CenteredRewardKernelLaw
      (contextIndependentOfActionLaws
        (Context := Context) armLaw hprob)
      (fun _ arm => armMean arm)
      (fun _ arm =>
        Concentration.intervalVarianceProxy (lo arm) (hi arm)) := by
  apply contextIndependentCenteredRewardKernelLaw_of_hasSubgaussianMGF
    armLaw hprob armMean
      (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm)) hmean
  intro arm
  haveI : IsProbabilityMeasure (armLaw arm) := hprob arm
  simpa [Rat.cast_sub] using
    (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
      (mu := armLaw arm)
      (X := fun reward : Rat => ((reward : Rat) : Real))
      (lo := lo arm)
      (hi := hi arm)
      (mean := ((armMean arm : Rat) : Real))
      (hmeas arm) (hbound arm) (hmean arm))

end RewardKernel
end BanditRLProof
