import BanditRLProof.Algorithms.UCBArmStreamExpectedPullCount
import BanditRLProof.Algorithms.UCBConditionalRewardPairTrajectorySampledAsymptotics
import Mathlib.Analysis.PSeries

/-!
# One-policy asymptotics for the canonical arm-stream UCB process

This module keeps one recursive `armStreamAction` and one `armStreamMeasure`
fixed across all horizons. At exploration scale `c = 4`, the finite tail term
in the exact LML-shaped regret bound is uniformly bounded by a convergent
NNReal p-series, yielding logarithmic expected regret and vanishing expected
average regret for the same policy and measure.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal Topology

namespace UCB

/-- The summable cubic tail that controls `indexTail 4`. -/
noncomputable def armStreamPSeriesTerm (t : Nat) : NNReal :=
  1 / (((t + 1 : Nat) : NNReal) ^ (3 : Real))

/-- A fixed finite upper bound for every `constSum 4 n`. -/
noncomputable def armStreamPSeriesTailBound : NNReal :=
  ∑' t : Nat, armStreamPSeriesTerm t

theorem armStreamPSeriesTerm_summable : Summable armStreamPSeriesTerm := by
  unfold armStreamPSeriesTerm
  exact (NNReal.summable_nat_add_iff 1).2
    (NNReal.summable_one_div_rpow.mpr (by norm_num : (1 : Real) < 3))

theorem indexTail_four_eq_coe_armStreamPSeriesTerm (t : Nat) :
    indexTail 4 t = (armStreamPSeriesTerm t : ENNReal) := by
  unfold indexTail armStreamPSeriesTerm
  norm_num

theorem constSum_four_le_armStreamPSeriesTailBound (n : Nat) :
    constSum 4 n <= (armStreamPSeriesTailBound : ENNReal) := by
  have hnn :
      (Finset.range n).sum armStreamPSeriesTerm <=
        armStreamPSeriesTailBound := by
    exact Summable.sum_le_tsum
      (s := Finset.range n) (fun _t _ht => zero_le _)
      armStreamPSeriesTerm_summable
  rw [constSum]
  simp_rw [indexTail_four_eq_coe_armStreamPSeriesTerm]
  exact_mod_cast hnn

theorem constSum_four_toReal_le_armStreamPSeriesTailBound (n : Nat) :
    (constSum 4 n).toReal <= (armStreamPSeriesTailBound : Real) := by
  rw [← ENNReal.coe_toReal armStreamPSeriesTailBound]
  exact
    (ENNReal.toReal_le_toReal (constSum_ne_top 4 n) (by simp)).2
      (constSum_four_le_armStreamPSeriesTailBound n)

/--
Fixed kernel-dependent coefficient for the one-policy logarithmic envelope.
-/
noncomputable def armStreamAsymptoticModelCoefficient {K : Nat}
    (nu : Kernel (Fin K) Real) (sigma2 : NNReal) : Real :=
  (Finset.univ : Finset (Fin K)).sum (fun arm =>
    32 * (sigma2 : Real) / realKernelGap nu arm +
      realKernelGap nu arm *
        (2 + 2 * (armStreamPSeriesTailBound : Real)))

theorem armStreamAsymptoticModelCoefficient_nonneg
    {K : Nat} (hK : 0 < K)
    (nu : Kernel (Fin K) Real) (sigma2 : NNReal) :
    0 <= armStreamAsymptoticModelCoefficient nu sigma2 := by
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
  unfold armStreamAsymptoticModelCoefficient
  apply Finset.sum_nonneg
  intro arm _harm
  have hgap : 0 <= realKernelGap nu arm := realKernelGap_nonneg nu arm
  have hfirst : 0 <= 32 * (sigma2 : Real) / realKernelGap nu arm :=
    div_nonneg (by positivity) hgap
  have hsecond :
      0 <= realKernelGap nu arm *
        (2 + 2 * (armStreamPSeriesTailBound : Real)) := by
    positivity
  linarith

theorem lml_sum_four_le_armStreamAsymptoticModelCoefficient
    {K : Nat} (hK : 0 < K)
    (nu : Kernel (Fin K) Real) (sigma2 : NNReal) (n : Nat) :
    (Finset.univ : Finset (Fin K)).sum (fun arm =>
        8 * 4 * (sigma2 : Real) * Real.log ((n + 1 : Nat) : Real) /
            realKernelGap nu arm +
          realKernelGap nu arm * (2 + 2 * (constSum 4 n).toReal)) <=
      armStreamAsymptoticModelCoefficient nu sigma2 *
        (1 + Real.log ((n + 1 : Nat) : Real)) := by
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
  have hlog : 0 <= Real.log ((n + 1 : Nat) : Real) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have htail := constSum_four_toReal_le_armStreamPSeriesTailBound n
  calc
    _ <= (Finset.univ : Finset (Fin K)).sum (fun arm =>
        (32 * (sigma2 : Real) / realKernelGap nu arm +
          realKernelGap nu arm *
            (2 + 2 * (armStreamPSeriesTailBound : Real))) *
          (1 + Real.log ((n + 1 : Nat) : Real))) := by
      apply Finset.sum_le_sum
      intro arm _harm
      have hgap : 0 <= realKernelGap nu arm := realKernelGap_nonneg nu arm
      by_cases hgapZero : realKernelGap nu arm = 0
      · simp [hgapZero]
      · have hA :
            0 <= 32 * (sigma2 : Real) / realKernelGap nu arm :=
          div_nonneg (by positivity) hgap
        have hB :
            0 <= realKernelGap nu arm *
              (2 + 2 * (armStreamPSeriesTailBound : Real)) := by
          positivity
        have htailTerm :
            realKernelGap nu arm * (2 + 2 * (constSum 4 n).toReal) <=
              realKernelGap nu arm *
                (2 + 2 * (armStreamPSeriesTailBound : Real)) := by
          gcongr
        calc
          8 * 4 * (sigma2 : Real) * Real.log ((n + 1 : Nat) : Real) /
                realKernelGap nu arm +
              realKernelGap nu arm * (2 + 2 * (constSum 4 n).toReal) =
              (32 * (sigma2 : Real) / realKernelGap nu arm) *
                  Real.log ((n + 1 : Nat) : Real) +
                realKernelGap nu arm *
                  (2 + 2 * (constSum 4 n).toReal) := by
            ring
          _ <= (32 * (sigma2 : Real) / realKernelGap nu arm) *
                  Real.log ((n + 1 : Nat) : Real) +
                realKernelGap nu arm *
                  (2 + 2 * (armStreamPSeriesTailBound : Real)) :=
            add_le_add_right htailTerm _
          _ <= (32 * (sigma2 : Real) / realKernelGap nu arm +
                  realKernelGap nu arm *
                    (2 + 2 * (armStreamPSeriesTailBound : Real))) *
                (1 + Real.log ((n + 1 : Nat) : Real)) := by
            nlinarith [
              mul_nonneg hA (show 0 <= (1 : Real) by norm_num),
              mul_nonneg hB hlog]
    _ = armStreamAsymptoticModelCoefficient nu sigma2 *
        (1 + Real.log ((n + 1 : Nat) : Real)) := by
      rw [armStreamAsymptoticModelCoefficient, Finset.sum_mul]

/-- Expected regret of one fixed recursive arm-stream UCB process. -/
noncomputable def armStreamExpectedRegret {K : Nat}
    (hK : 0 < K) (sigma2 : NNReal) (nu : Kernel (Fin K) Real)
    [IsMarkovKernel nu] (n : Nat) : Real :=
  ∫ stream : ArmRewardStream K,
    realKernelRegret nu
      (armStreamAction hK (4 * (sigma2 : Real)) stream) n
    ∂armStreamMeasure nu

theorem armStreamExpectedRegret_nonneg_and_le
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (hsigma2 : sigma2 ≠ 0)
    (hsubG : ∀ arm : Fin K, HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm))
    (n : Nat) :
    0 <= armStreamExpectedRegret hK sigma2 nu n ∧
      armStreamExpectedRegret hK sigma2 nu n <=
        armStreamAsymptoticModelCoefficient nu sigma2 *
          (1 + Real.log ((n + 1 : Nat) : Real)) := by
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
  constructor
  · unfold armStreamExpectedRegret
    refine integral_nonneg (fun stream => ?_)
    change 0 <= realKernelRegret nu
      (armStreamAction hK (4 * (sigma2 : Real)) stream) n
    rw [realKernelRegret_eq_finset_sum_gap]
    exact Finset.sum_nonneg fun _t _ht => realKernelGap_nonneg nu _
  · unfold armStreamExpectedRegret
    refine (integral_realKernelRegret_armStreamAction_le_lml_sum
      hK 4 sigma2 nu n (by norm_num) hsigma2 hsubG).trans ?_
    exact lml_sum_four_le_armStreamAsymptoticModelCoefficient
      hK nu sigma2 n

theorem armStreamExpectedRegret_isBigO_log
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (hsigma2 : sigma2 ≠ 0)
    (hsubG : ∀ arm : Fin K, HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm)) :
    (armStreamExpectedRegret hK sigma2 nu) =O[atTop]
      (fun n : Nat => Real.log ((n + 1 : Nat) : Real)) := by
  have hcoefficient :=
    armStreamAsymptoticModelCoefficient_nonneg hK nu sigma2
  have henvelope :
      (fun n : Nat => armStreamAsymptoticModelCoefficient nu sigma2 *
        (1 + Real.log ((n + 1 : Nat) : Real))) =O[atTop]
      (fun n : Nat => Real.log ((n + 1 : Nat) : Real)) := by
    simpa using
      one_add_log_natCast_succ_isBigO_log_natCast_succ.const_mul_left
        (armStreamAsymptoticModelCoefficient nu sigma2)
  rw [Asymptotics.isBigO_iff] at henvelope ⊢
  obtain ⟨c, hc⟩ := henvelope
  refine ⟨c, ?_⟩
  filter_upwards [hc] with n henvelopeN
  have hpoint :=
    armStreamExpectedRegret_nonneg_and_le
      hK sigma2 nu hsigma2 hsubG n
  have henvelopeNonneg :
      0 <= armStreamAsymptoticModelCoefficient nu sigma2 *
        (1 + Real.log ((n + 1 : Nat) : Real)) := by
    exact mul_nonneg hcoefficient
      (add_nonneg zero_le_one (Real.log_nonneg (by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))))
  calc
    ‖armStreamExpectedRegret hK sigma2 nu n‖ =
        armStreamExpectedRegret hK sigma2 nu n :=
      Real.norm_of_nonneg hpoint.1
    _ <= armStreamAsymptoticModelCoefficient nu sigma2 *
        (1 + Real.log ((n + 1 : Nat) : Real)) := hpoint.2
    _ = ‖armStreamAsymptoticModelCoefficient nu sigma2 *
        (1 + Real.log ((n + 1 : Nat) : Real))‖ :=
      (Real.norm_of_nonneg henvelopeNonneg).symm
    _ <= c * ‖Real.log ((n + 1 : Nat) : Real)‖ := henvelopeN

theorem armStreamExpectedRegret_isLittleO_natCast_succ
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (hsigma2 : sigma2 ≠ 0)
    (hsubG : ∀ arm : Fin K, HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm)) :
    (armStreamExpectedRegret hK sigma2 nu) =o[atTop]
      (fun n : Nat => ((n + 1 : Nat) : Real)) :=
  (armStreamExpectedRegret_isBigO_log
    hK sigma2 nu hsigma2 hsubG).trans_isLittleO
      log_natCast_succ_isLittleO_natCast_succ

/-- Expected regret of the fixed arm-stream policy normalized by `n + 1`. -/
noncomputable def armStreamExpectedAverageRegret {K : Nat}
    (hK : 0 < K) (sigma2 : NNReal) (nu : Kernel (Fin K) Real)
    [IsMarkovKernel nu] (n : Nat) : Real :=
  armStreamExpectedRegret hK sigma2 nu n / ((n + 1 : Nat) : Real)

/--
One fixed canonical arm-stream UCB policy has vanishing expected average
regret under its one fixed product measure.
-/
theorem armStreamExpectedAverageRegret_tendsto_zero
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (hsigma2 : sigma2 ≠ 0)
    (hsubG : ∀ arm : Fin K, HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm)) :
    Tendsto (armStreamExpectedAverageRegret hK sigma2 nu)
      atTop (nhds 0) := by
  have hlimit :=
    (armStreamExpectedRegret_isLittleO_natCast_succ
      hK sigma2 nu hsigma2 hsubG).tendsto_div_nhds_zero
  convert hlimit using 1

end UCB
end BanditRLProof
