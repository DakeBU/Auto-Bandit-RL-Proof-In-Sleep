import BanditRLProof

/-!
# Typed public canary for Part IV, Chapter 17

The examples exercise the compiled Theorem 17.1 and Corollaries 17.2--17.3 stochastic
terminals, the first-moment and probability leaves, the shared-noise clipped
construction, and construction-level Eq. (17.8). The adversarial checks use
the user-approved non-strict Claim 17.6, exact Claim 17.7, and corrected
Theorem 17.4 on `0 < delta <= 1/32`, with explicit `c=1/160`, `C=64`.
-/

namespace BanditRLProof
namespace LowerBounds

open MeasureTheory Set

example {m : Nat} (hm : 0 < m)
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real) (n : Nat)
    (delta : Real) (hd : 0 < delta) (hd32 : delta <= 1 / 32)
    (horizon : 64 * ((m + 1 : Nat) : Real) * Real.log (1 / (2 * delta)) <= ((n + 1 : Nat) : Real)) :
    ∃ table : AdversarialRewardTable (m + 1),
      (∀ t arm, table t arm ∈ Set.Icc (0 : Real) 1) ∧
      delta <= 1 - adversarialTableCDF algorithm table n
        (adversarialHighProbabilityThreshold (n + 1) (m + 1) (1 / 160) delta) := by
  exact adversarialRandomRegret_ge_theorem17_4 hm algorithm n delta hd hd32 horizon

example {Omega : Type*} (quantity : Omega -> Real) (threshold : Real)
    (omega : Omega) :
    omega ∈ tailAtLeast quantity threshold ↔ threshold <= quantity omega := by
  rfl

example {Instance : Type*} [MeasurableSpace Instance]
    (Q : Measure Instance) [IsProbabilityMeasure Q]
    (tailMass : Instance -> Real) (delta : Real)
    (hIntegrable : Integrable tailMass Q)
    (hAverage : delta <= ∫ x, tailMass x ∂Q) :
    exists x, delta <= tailMass x := by
  exact exists_tailMass_ge_of_integral_ge Q tailMass delta hIntegrable hAverage

example {Instance : Type*} [MeasurableSpace Instance]
    (Q : Measure Instance) [IsProbabilityMeasure Q]
    (cdf : Instance -> Real -> Real) (threshold delta : Real)
    (hIntegrable : Integrable (fun x => 1 - cdf x threshold) Q)
    (hAverage : delta <= ∫ x, 1 - cdf x threshold ∂Q) :
    exists x, delta <= 1 - cdf x threshold := by
  exact exists_cdfTail_ge_of_integral_ge Q cdf threshold delta
    hIntegrable hAverage

example {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (pullSmall clippingBad : Set Omega) (delta : Real)
    (hPullSmall : 2 * delta <= P.real pullSmall)
    (hClippingBad : P.real clippingBad <= delta) :
    delta <= P.real (pullSmall \ clippingBad) := by
  exact measureReal_diff_ge_delta P pullSmall clippingBad delta
    hPullSmall hClippingBad

example (gap : Real) (hGap : 0 <= gap) :
    gap * ((8 : Real) / 4) <=
      adversarialRegretLowerExpression 8 4 2 gap := by
  exact adversarialRegretLowerExpression_ge_quarter 8 4 2 gap hGap
    (by norm_num) (by norm_num)

example (horizon alternativeArms : Nat) (B delta : Real) :
    stochasticHighProbabilityThreshold horizon alternativeArms B delta =
      (1 / 4 : Real) *
        min (horizon : Real)
          ((1 / B) *
            Real.sqrt ((alternativeArms : Real) * (horizon : Real)) *
            Real.log (1 / (4 * delta))) := by
  rfl

example (horizon alternativeArms : Nat) (delta : Real) :
    stochasticMinimaxHighProbabilityThreshold horizon alternativeArms delta =
      (1 / 4 : Real) *
        min (horizon : Real)
          (Real.sqrt
            (((horizon : Real) * (alternativeArms : Real) / 2) *
              Real.log (1 / (4 * delta)))) := by
  rfl

example (horizon arms : Nat) (c delta : Real) :
    adversarialHighProbabilityThreshold horizon arms c delta =
      c * Real.sqrt
        ((horizon : Real) * (arms : Real) * Real.log (1 / (2 * delta))) := by
  rfl

example (gap randomRegret : Real) (hGap : 0 <= gap)
    (hSource : adversarialRegretLowerExpression 8 4 2 gap <= randomRegret) :
    gap * ((8 : Real) / 4) <= randomRegret := by
  exact randomRegret_ge_quarter_of_clippingDecomposition
    8 4 2 gap randomRegret hGap (by norm_num) (by norm_num) hSource

#check gaussianRandomPseudoRegret_ge_theorem17_1
#check gaussianRandomPseudoRegret_ge_corollary17_2
#check noUniformGaussianRandomPseudoRegretTail_corollary17_3
#check integral_exp_neg_rpow_inv_le_one
#check integral_le_scale_of_all_rpow_log_tail
#check gapOneGaussianRandomPseudoRegret
#check adversarialCenteredNoiseLaw
#check adversarialClippedHistoryLaw
#check adversarialClipHistoryAlgorithm
#check adversarialClipHistory_pullCountReal
#check adversarialClipped_initialPairLaw
#check adversarialClippedHistoryLaw_zero
#check adversarialClipped_historyStepLaw
#check adversarialClippedHistoryLaw_eq_map
#check adversarialClippedHistoryLaw_pullSmall
#check klDiv_adversarialUnclipped_base_changed_history
#check adversarialFullHardShift
#check adversarialFullRandomRegret_ge_boundary_eq17_8
#check adversarialFullBoundaryCount_tail_claim17_7
#check adversarialTableHistoryKernel
#check adversarialTableHistoryKernel_isMarkov
#check adversarialTableStepKernel_apply
#check adversarialTableHistoryKernel_prefix_congr
#check adversarialNoiseHistoryJoint
#check adversarialNoiseHistoryJoint_noise_marginal
#check adversarialNoiseHistoryKernel_update_future
#check adversarialCenteredNoiseLaw_split
#check adversarialNoiseHistoryKernel_split_future
#check lintegral_adversarialCenteredNoiseLaw_split
#check adversarialNoiseHistoryJoint_history_marginal_zero
#check lintegral_adversarialTableHistoryKernel_succ
#check lintegral_adversarialFreshNoise_step
#check lintegral_adversarialNoiseHistoryKernel_succ_slice
#check adversarialNoiseHistoryJoint_history_marginal
#check adversarialNoiseHistoryJoint_pull_le_half_claim17_6
#check adversarialNoiseHistoryJoint_good_event
#check adversarialHistoryActions_pullCountReal
#check adversarialNoiseHistoryJoint_randomRegret_tail
#check exists_adversarialTable_randomRegret_tail
#check exists_adversarialTable_randomRegret_gt_theorem17_4
#check adversarialTableExpectedRegret
#check integrable_adversarialTableRandomRegret
#check adversarialTable_strictTail_eq_one_sub_CDF
#check adversarialRandomRegret_ge_theorem17_4
#print axioms LowerBounds.integrable_adversarialTableRandomRegret
#print axioms LowerBounds.adversarialRandomRegret_ge_theorem17_4
#print axioms LowerBounds.exists_adversarialTable_randomRegret_gt_theorem17_4
#check adversarialClaim17_6Gap_information_calibration
#check adversarialClippedHistory_pull_le_half_claim17_6
#print axioms LowerBounds.adversarialClippedHistory_pull_le_half_claim17_6

-- At confidence 3/4 the printed Theorem 17.4 threshold collapses to zero,
-- while a uniform one-round choice has positive regret with probability at most 1/2.
example (x y : Real) :
    ((if 0 < max x y - x then (1 : Real) else 0) +
      (if 0 < max x y - y then (1 : Real) else 0)) / 2 <= 1 / 2 := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]
    simp only [sub_self, lt_self_iff_false, if_false, add_zero]
    split <;> norm_num
  · rw [max_eq_left h]
    simp only [sub_self, lt_self_iff_false, if_false, zero_add]
    split <;> norm_num

example (c C : Real) (hC : 0 < C) :
    (1 : Real) >= C * 2 * Real.log (1 / (2 * (3 / 4 : Real))) ∧
    c * Real.sqrt (1 * 2 * Real.log (1 / (2 * (3 / 4 : Real)))) = 0 := by
  have hl : Real.log (1 / (2 * (3 / 4 : Real))) <= 0 := by
    apply Real.log_nonpos <;> norm_num
  constructor
  · have hp := mul_nonpos_of_nonneg_of_nonpos (show 0 <= C * 2 by positivity) hl
    linarith
  · rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith)]
    simp

-- Source obstruction: a fixed two-round schedule pulls each arm once.
-- The literal strict Claim 17.6 event is empty for both arms.
example (arm : Fin 2) :
    (∑ t : Fin 2, if t = arm then (1 : Real) else 0) = 1 := by simp

example (P : MeasureTheory.Measure Unit) (arm : Fin 2) :
    P { _u | (∑ t : Fin 2, if t = arm then (1 : Real) else 0) < (2 : Real) / 2 } = 0 := by
  simp
#check adversarialCenteredNoiseLaw_reward_marginal
#check adversarialClaim17_6Gap
#check adversarialRandomRegret_ge_eq17_8
#check adversarialClippingCount_tail_claim17_7
#check adversarialBoundaryClippingCount_tail_claim17_7
#check adversarialRandomRegret_ge_boundary_eq17_8
#print axioms LowerBounds.adversarialRandomRegret_ge_boundary_eq17_8
#print axioms LowerBounds.adversarialBoundaryClippingCount_tail_claim17_7
#print axioms LowerBounds.adversarialClippingCount_tail_claim17_7

#print axioms LowerBounds.gaussianRandomPseudoRegret_ge_theorem17_1
#print axioms LowerBounds.gaussianRandomPseudoRegret_ge_corollary17_2
#print axioms LowerBounds.noUniformGaussianRandomPseudoRegretTail_corollary17_3
#print axioms LowerBounds.integral_exp_neg_rpow_inv_le_one
#print axioms LowerBounds.exists_tailMass_ge_of_integral_ge
#print axioms LowerBounds.exists_cdfTail_ge_of_integral_ge
#print axioms LowerBounds.measureReal_diff_ge_delta
#print axioms LowerBounds.adversarialRegretLowerExpression_ge_quarter
#print axioms LowerBounds.randomRegret_ge_quarter_of_clippingDecomposition
#print axioms LowerBounds.adversarialRandomRegret_ge_eq17_8

end LowerBounds
end BanditRLProof
