import BanditRLProof.Algorithms.UCBArmStreamAsymptotics
import BanditRLProof.FiniteArmRewardKernelLaw

/-!
# Practical finite-arm reward laws for one-policy arm-stream UCB

This module packages stationary Real-valued arm laws as a Mathlib kernel and
instantiates the canonical arm-stream expected-consistency theorem. The final
bounded-law endpoint keeps one recursive policy and one product measure fixed
across all horizons.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal Topology

namespace UCB

/-- A finite family of Real reward laws, viewed as an arm-indexed kernel. -/
noncomputable def finiteArmRealRewardKernel {K : Nat}
    (armLaw : Fin K -> Measure Real) : Kernel (Fin K) Real :=
  Kernel.ofFunOfCountable armLaw

@[simp]
theorem finiteArmRealRewardKernel_apply {K : Nat}
    (armLaw : Fin K -> Measure Real) (arm : Fin K) :
    finiteArmRealRewardKernel armLaw arm = armLaw arm :=
  rfl

/-- Pointwise probability laws make the finite-arm kernel Markov. -/
theorem finiteArmRealRewardKernel_isMarkov {K : Nat}
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm)) :
    IsMarkovKernel (finiteArmRealRewardKernel armLaw) where
  isProbabilityMeasure arm := by
    simpa using hprob arm

/--
Expected regret of the canonical one-policy arm-stream process built from
direct finite-arm sub-Gaussian laws. The common tuning proxy is the padded
finite maximum of the genuine armwise proxies.
-/
noncomputable def armStreamFiniteArmSubgaussianExpectedRegret
    {K : Nat} (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (varianceProxy : Fin K -> NNReal) (n : Nat) : Real :=
  let nu := finiteArmRealRewardKernel armLaw
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy varianceProxy
  letI : IsMarkovKernel nu := finiteArmRealRewardKernel_isMarkov armLaw hprob
  armStreamExpectedRegret hK sigma2 nu n

/-- Direct finite-arm sub-Gaussian laws satisfy the fixed logarithmic envelope. -/
theorem armStreamFiniteArmSubgaussianExpectedRegret_nonneg_and_le
    {K : Nat} (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (varianceProxy : Fin K -> NNReal)
    (hsubG : forall arm,
      HasSubgaussianMGF
        (fun reward : Real => reward - integral (armLaw arm) id)
        (varianceProxy arm) (armLaw arm))
    (n : Nat) :
    let nu := finiteArmRealRewardKernel armLaw
    let sigma2 := Concentration.finiteArmPositiveVarianceProxy varianceProxy
    0 <= armStreamFiniteArmSubgaussianExpectedRegret
        hK armLaw hprob varianceProxy n /\
      armStreamFiniteArmSubgaussianExpectedRegret
          hK armLaw hprob varianceProxy n <=
        armStreamAsymptoticModelCoefficient nu sigma2 *
          (1 + Real.log ((n + 1 : Nat) : Real)) := by
  let nu := finiteArmRealRewardKernel armLaw
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy varianceProxy
  letI : IsMarkovKernel nu := finiteArmRealRewardKernel_isMarkov armLaw hprob
  have hsigma2 : sigma2 ≠ 0 := by
    have hpos :=
      Concentration.finiteArmPositiveVarianceProxy_pos varianceProxy
    exact_mod_cast (ne_of_gt hpos)
  have hsubGCommon : forall arm : Fin K,
      HasSubgaussianMGF
        (fun reward => reward - realKernelMean nu arm)
        sigma2 (nu arm) := by
    intro arm
    simpa [nu, realKernelMean] using
      (ConditionalExpectationReward.hasSubgaussianMGF_mono_varianceProxy
        (Concentration.varianceProxy_le_finiteArmPositiveVarianceProxy
          varianceProxy arm)
        (hsubG arm))
  simpa [armStreamFiniteArmSubgaussianExpectedRegret, nu, sigma2] using
    (armStreamExpectedRegret_nonneg_and_le
      hK sigma2 nu hsigma2 hsubGCommon n)

/-- Direct finite-arm sub-Gaussian expected regret normalized by `n + 1`. -/
noncomputable def armStreamFiniteArmSubgaussianExpectedAverageRegret
    {K : Nat} (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (varianceProxy : Fin K -> NNReal) (n : Nat) : Real :=
  armStreamFiniteArmSubgaussianExpectedRegret
      hK armLaw hprob varianceProxy n /
    ((n + 1 : Nat) : Real)

/--
Direct stationary finite-arm sub-Gaussian laws instantiate one fixed canonical
arm-stream policy with vanishing expected average regret.
-/
theorem armStreamFiniteArmSubgaussianExpectedAverageRegret_tendsto_zero
    {K : Nat} (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (varianceProxy : Fin K -> NNReal)
    (hsubG : forall arm,
      HasSubgaussianMGF
        (fun reward : Real => reward - integral (armLaw arm) id)
        (varianceProxy arm) (armLaw arm)) :
    Tendsto
      (armStreamFiniteArmSubgaussianExpectedAverageRegret
        hK armLaw hprob varianceProxy)
      atTop (nhds 0) := by
  let nu := finiteArmRealRewardKernel armLaw
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy varianceProxy
  letI : IsMarkovKernel nu := finiteArmRealRewardKernel_isMarkov armLaw hprob
  have hsigma2 : sigma2 ≠ 0 := by
    have hpos :=
      Concentration.finiteArmPositiveVarianceProxy_pos varianceProxy
    exact_mod_cast (ne_of_gt hpos)
  have hsubGCommon : forall arm : Fin K,
      HasSubgaussianMGF
        (fun reward => reward - realKernelMean nu arm)
        sigma2 (nu arm) := by
    intro arm
    simpa [nu, realKernelMean] using
      (ConditionalExpectationReward.hasSubgaussianMGF_mono_varianceProxy
        (Concentration.varianceProxy_le_finiteArmPositiveVarianceProxy
          varianceProxy arm)
        (hsubG arm))
  simpa [armStreamFiniteArmSubgaussianExpectedAverageRegret,
    armStreamFiniteArmSubgaussianExpectedRegret, armStreamExpectedAverageRegret,
    nu, sigma2] using
      (armStreamExpectedAverageRegret_tendsto_zero
        hK sigma2 nu hsigma2 hsubGCommon)

/-- Expected regret of the one-policy process for common-bounded arm laws. -/
noncomputable def armStreamBoundedFiniteArmExpectedRegret
    {K : Nat} (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real) (n : Nat) : Real :=
  armStreamFiniteArmSubgaussianExpectedRegret hK armLaw hprob
    (fun _ => Concentration.intervalVarianceProxy lo hi) n

/-- Common-bounded finite-arm laws satisfy the fixed logarithmic envelope. -/
theorem armStreamBoundedFiniteArmExpectedRegret_nonneg_and_le
    {K : Nat} (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Real => Set.Icc lo hi reward) (ae (armLaw arm)))
    (n : Nat) :
    let nu := finiteArmRealRewardKernel armLaw
    let sigma2 := Concentration.finiteArmPositiveVarianceProxy
      (fun _ : Fin K => Concentration.intervalVarianceProxy lo hi)
    0 <= armStreamBoundedFiniteArmExpectedRegret
        hK armLaw hprob lo hi n /\
      armStreamBoundedFiniteArmExpectedRegret hK armLaw hprob lo hi n <=
        armStreamAsymptoticModelCoefficient nu sigma2 *
          (1 + Real.log ((n + 1 : Nat) : Real)) := by
  have hsubG : forall arm : Fin K,
      HasSubgaussianMGF
        (fun reward : Real => reward - integral (armLaw arm) id)
        (Concentration.intervalVarianceProxy lo hi) (armLaw arm) := by
    intro arm
    letI : IsProbabilityMeasure (armLaw arm) := hprob arm
    simpa using
      (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
        (mu := armLaw arm) (X := id)
        (mean := integral (armLaw arm) id)
        measurable_id.aemeasurable (hbound arm) rfl)
  simpa [armStreamBoundedFiniteArmExpectedRegret] using
    (armStreamFiniteArmSubgaussianExpectedRegret_nonneg_and_le
      hK armLaw hprob
        (fun _ => Concentration.intervalVarianceProxy lo hi) hsubG n)

/-- Expected common-bounded one-policy regret normalized by `n + 1`. -/
noncomputable def armStreamBoundedFiniteArmExpectedAverageRegret
    {K : Nat} (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real) (n : Nat) : Real :=
  armStreamBoundedFiniteArmExpectedRegret hK armLaw hprob lo hi n /
    ((n + 1 : Nat) : Real)

/--
Stationary finite-arm Real reward laws bounded almost surely in one common
interval induce one fixed canonical UCB process with vanishing expected average
regret. The positive padded tuning proxy removes any `lo < hi` premise.
-/
theorem armStreamBoundedFiniteArmExpectedAverageRegret_tendsto_zero
    {K : Nat} (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Real => Set.Icc lo hi reward) (ae (armLaw arm))) :
    Tendsto
      (armStreamBoundedFiniteArmExpectedAverageRegret
        hK armLaw hprob lo hi)
      atTop (nhds 0) := by
  have hsubG : forall arm : Fin K,
      HasSubgaussianMGF
        (fun reward : Real => reward - integral (armLaw arm) id)
        (Concentration.intervalVarianceProxy lo hi) (armLaw arm) := by
    intro arm
    letI : IsProbabilityMeasure (armLaw arm) := hprob arm
    simpa using
      (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
        (mu := armLaw arm) (X := id)
        (mean := integral (armLaw arm) id)
        measurable_id.aemeasurable (hbound arm) rfl)
  simpa [armStreamBoundedFiniteArmExpectedAverageRegret,
    armStreamBoundedFiniteArmExpectedRegret] using
      (armStreamFiniteArmSubgaussianExpectedAverageRegret_tendsto_zero
        hK armLaw hprob
          (fun _ => Concentration.intervalVarianceProxy lo hi) hsubG)

/-- Expected regret of the one-policy process for armwise-bounded laws. -/
noncomputable def armStreamArmwiseBoundedFiniteArmExpectedRegret
    {K : Nat} (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real) (n : Nat) : Real :=
  armStreamFiniteArmSubgaussianExpectedRegret hK armLaw hprob
    (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm)) n

/-- Armwise-bounded finite-arm laws satisfy the fixed logarithmic envelope. -/
theorem armStreamArmwiseBoundedFiniteArmExpectedRegret_nonneg_and_le
    {K : Nat} (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Real => Set.Icc (lo arm) (hi arm) reward)
        (ae (armLaw arm)))
    (n : Nat) :
    let nu := finiteArmRealRewardKernel armLaw
    let sigma2 := Concentration.finiteArmPositiveVarianceProxy
      (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
    0 <= armStreamArmwiseBoundedFiniteArmExpectedRegret
        hK armLaw hprob lo hi n /\
      armStreamArmwiseBoundedFiniteArmExpectedRegret
          hK armLaw hprob lo hi n <=
        armStreamAsymptoticModelCoefficient nu sigma2 *
          (1 + Real.log ((n + 1 : Nat) : Real)) := by
  have hsubG : forall arm : Fin K,
      HasSubgaussianMGF
        (fun reward : Real => reward - integral (armLaw arm) id)
        (Concentration.intervalVarianceProxy (lo arm) (hi arm))
        (armLaw arm) := by
    intro arm
    letI : IsProbabilityMeasure (armLaw arm) := hprob arm
    simpa using
      (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
        (mu := armLaw arm) (X := id)
        (lo := lo arm) (hi := hi arm)
        (mean := integral (armLaw arm) id)
        measurable_id.aemeasurable (hbound arm) rfl)
  simpa [armStreamArmwiseBoundedFiniteArmExpectedRegret] using
    (armStreamFiniteArmSubgaussianExpectedRegret_nonneg_and_le
      hK armLaw hprob
        (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
        hsubG n)

/-- Expected armwise-bounded one-policy regret normalized by `n + 1`. -/
noncomputable def armStreamArmwiseBoundedFiniteArmExpectedAverageRegret
    {K : Nat} (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real) (n : Nat) : Real :=
  armStreamArmwiseBoundedFiniteArmExpectedRegret
      hK armLaw hprob lo hi n /
    ((n + 1 : Nat) : Real)

/--
Stationary finite-arm Real reward laws with arm-dependent almost-sure interval
bounds induce one fixed canonical UCB process with vanishing expected average
regret. Positive padding removes every pointwise interval-order premise.
-/
theorem armStreamArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero
    {K : Nat} (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Real => Set.Icc (lo arm) (hi arm) reward)
        (ae (armLaw arm))) :
    Tendsto
      (armStreamArmwiseBoundedFiniteArmExpectedAverageRegret
        hK armLaw hprob lo hi)
      atTop (nhds 0) := by
  have hsubG : forall arm : Fin K,
      HasSubgaussianMGF
        (fun reward : Real => reward - integral (armLaw arm) id)
        (Concentration.intervalVarianceProxy (lo arm) (hi arm))
        (armLaw arm) := by
    intro arm
    letI : IsProbabilityMeasure (armLaw arm) := hprob arm
    simpa using
      (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
        (mu := armLaw arm) (X := id)
        (lo := lo arm) (hi := hi arm)
        (mean := integral (armLaw arm) id)
        measurable_id.aemeasurable (hbound arm) rfl)
  simpa [armStreamArmwiseBoundedFiniteArmExpectedAverageRegret,
    armStreamArmwiseBoundedFiniteArmExpectedRegret] using
      (armStreamFiniteArmSubgaussianExpectedAverageRegret_tendsto_zero
        hK armLaw hprob
          (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
          hsubG)

end UCB
end BanditRLProof
