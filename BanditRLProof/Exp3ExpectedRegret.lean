import BanditRLProof.Exp3PredictableIntegration

/-!
# Tuned predictable EXP3 regret

This module keeps parameter algebra separate from the generated trajectory and
conditional-law proof.  The first theorem simplifies the unoptimized budget
when `eta = gamma / |A|`; the second applies that deterministic fact to the
compiled predictable EXP3 endpoint.
-/

namespace BanditRLProof
namespace Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Deterministic EXP3 parameter algebra.  If `eta = gamma / K`, exploration
is at most one half, and `gamma^2 T` covers `K log K`, then the unoptimized
budget is at most `4 gamma T`. -/
theorem expectedRegretBudget_le_four_mul_gamma_mul_horizon
    (K T logK eta gamma : Real)
    (hK : 0 < K) (hT : 0 <= T)
    (hgamma_pos : 0 < gamma) (hgamma_le_half : gamma <= 1 / 2)
    (heta : eta = gamma / K)
    (hlog_budget : K * logK <= gamma ^ 2 * T) :
    logK / eta + (eta * (1 / (1 - gamma))) * (K * T) + gamma * T <=
      4 * gamma * T := by
  have hK_ne : K ≠ 0 := ne_of_gt hK
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
  have hone_sub_pos : 0 < 1 - gamma := by nlinarith
  have hfirst_eq : logK / (gamma / K) = K * logK / gamma := by
    field_simp [hK_ne, hgamma_ne]
  have hfirst : logK / (gamma / K) <= gamma * T := by
    rw [hfirst_eq, div_le_iff₀ hgamma_pos]
    nlinarith [hlog_budget]
  have hsecond_eq :
      ((gamma / K) * (1 / (1 - gamma))) * (K * T) =
        gamma * T / (1 - gamma) := by
    field_simp [hK_ne, ne_of_gt hone_sub_pos]
  have hgammaT_nonneg : 0 <= gamma * T := mul_nonneg hgamma_pos.le hT
  have hone_sub_two_gamma_nonneg : 0 <= 1 - 2 * gamma := by
    nlinarith
  have hsecond :
      ((gamma / K) * (1 / (1 - gamma))) * (K * T) <=
        2 * gamma * T := by
    rw [hsecond_eq, div_le_iff₀ hone_sub_pos]
    nlinarith [mul_nonneg hgammaT_nonneg hone_sub_two_gamma_nonneg]
  rw [heta]
  linarith

/-- Square-root exploration scale used by the tuned corollary. -/
noncomputable def tunedExplorationRate (K T : Real) : Real :=
  Real.sqrt (K * Real.log K / T)

/-- Learning rate paired with `tunedExplorationRate`. -/
noncomputable def tunedLearningRate (K T : Real) : Real :=
  tunedExplorationRate K T / K

theorem tunedExplorationRate_pos
    (K T : Real) (hK_one : 1 < K) (hT : 0 < T) :
    0 < tunedExplorationRate K T := by
  apply Real.sqrt_pos.2
  exact div_pos (mul_pos (by linarith) (Real.log_pos hK_one)) hT

theorem tunedExplorationRate_le_half
    (K T : Real) (hT : 0 < T)
    (hscale : 4 * K * Real.log K <= T) :
    tunedExplorationRate K T <= 1 / 2 := by
  rw [tunedExplorationRate, Real.sqrt_le_iff]
  constructor
  · norm_num
  rw [div_le_iff₀ hT]
  nlinarith

theorem tunedLearningRate_pos
    (K T : Real) (hK_one : 1 < K) (hT : 0 < T) :
    0 < tunedLearningRate K T := by
  exact div_pos (tunedExplorationRate_pos K T hK_one hT) (by linarith)

theorem tunedExplorationRate_sq_mul_eq
    (K T : Real) (hK_one : 1 < K) (hT : 0 < T) :
    tunedExplorationRate K T ^ 2 * T = K * Real.log K := by
  rw [tunedExplorationRate,
    Real.sq_sqrt (div_nonneg
      (mul_nonneg (by linarith) (Real.log_pos hK_one).le) hT.le)]
  field_simp [ne_of_gt hT]

theorem tunedExplorationRate_mul_eq_sqrt_mul
    (K T : Real) (hK_one : 1 < K) (hT : 0 < T) :
    tunedExplorationRate K T * T =
      Real.sqrt (K * T * Real.log K) := by
  have hK : 0 <= K := by linarith
  have hlog : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hsqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  rw [tunedExplorationRate, Real.sqrt_div' _ hT.le]
  calc
    Real.sqrt (K * Real.log K) / Real.sqrt T * T =
        Real.sqrt (K * Real.log K) * Real.sqrt T := by
      field_simp [ne_of_gt hsqrtT_pos]
      rw [Real.sq_sqrt hT.le]
    _ = Real.sqrt ((K * Real.log K) * T) := by
      rw [Real.sqrt_mul (mul_nonneg hK hlog)]
    _ = Real.sqrt (K * T * Real.log K) := by ring_nf

/-- The generated predictable EXP3 trajectory has regret at most
`4 gamma horizon` when `eta = gamma / |arms|` and the exploration budget
dominates `|arms| log |arms|`. -/
theorem sampledPredictable_expectedRegret_le_four_mul_gamma_mul_horizon
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (hlog_budget :
      (arms.card : Real) * Real.log arms.card <=
        gamma ^ 2 * (horizon : Real))
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let eta := gamma / (arms.card : Real)
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith) loss.environment
    integral mu (fun sample =>
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryExploredPredictableLossAt
            arms eta gamma loss t sample) -
        (Finset.range horizon).sum (fun t =>
          predictableLossAt loss t sample comparator)) <=
      4 * gamma * (horizon : Real) := by
  dsimp only
  have hcard_pos : 0 < (arms.card : Real) := by
    exact_mod_cast harms.card_pos
  have heta_pos : 0 < gamma / (arms.card : Real) :=
    div_pos hgamma_pos hcard_pos
  have hgamma_lt_one : gamma < 1 := by linarith
  have hbase := sampledPredictable_expectedRegret_le
    prior arms harms (gamma / (arms.card : Real)) gamma heta_pos
      hgamma_pos hgamma_lt_one loss horizon comparator hcomparator
  dsimp only at hbase
  exact hbase.trans
    (expectedRegretBudget_le_four_mul_gamma_mul_horizon
      (arms.card : Real) (horizon : Real) (Real.log arms.card)
      (gamma / (arms.card : Real)) gamma hcard_pos (Nat.cast_nonneg _)
      hgamma_pos hgamma_le_half rfl hlog_budget)

/-- Generated predictable EXP3 kernel at the square-root exploration and
learning rates.  The large-horizon hypotheses discharge the kernel's
`0 <= gamma <= 1` contract internally. -/
noncomputable def tunedPredictableTrajectoryKernel
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Nonempty Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (hhorizon_pos : 0 < horizon)
    (hscale :
      4 * (arms.card : Real) * Real.log arms.card <= (horizon : Real)) :
    Kernel Env (Nat -> Action × Real) :=
  sampledImportanceWeightedTrajectoryKernel arms harms
    (tunedLearningRate (arms.card : Real) (horizon : Real))
    (tunedExplorationRate (arms.card : Real) (horizon : Real))
    (tunedExplorationRate_pos (arms.card : Real) (horizon : Real)
      (by
        have htwo : (2 : Real) <= (arms.card : Real) := by
          exact_mod_cast hcard_two
        linarith)
      (by exact_mod_cast hhorizon_pos)).le
    ((tunedExplorationRate_le_half (arms.card : Real) (horizon : Real)
      (by exact_mod_cast hhorizon_pos) hscale).trans (by norm_num))
    loss.environment

/-- Tuned generated-trajectory expected predictable-regret bound.  Under the
large-horizon regime `4 |A| log |A| <= T`, the square-root exploration and
learning rates give the classical `sqrt(|A| T log |A|)` scale. -/
theorem sampledPredictable_expectedRegret_le_four_mul_sqrt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action) (horizon : Nat)
    (hhorizon_pos : 0 < horizon)
    (hscale :
      4 * (arms.card : Real) * Real.log arms.card <= (horizon : Real))
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let K := (arms.card : Real)
    let T := (horizon : Real)
    let gamma := tunedExplorationRate K T
    let eta := tunedLearningRate K T
    let mu := prior ⊗ₘ tunedPredictableTrajectoryKernel
      arms harms hcard_two loss horizon hhorizon_pos hscale
    integral mu (fun sample =>
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryExploredPredictableLossAt
            arms eta gamma loss t sample) -
        (Finset.range horizon).sum (fun t =>
          predictableLossAt loss t sample comparator)) <=
      4 * Real.sqrt (K * T * Real.log K) := by
  dsimp only
  have hK_one : 1 < (arms.card : Real) := by exact_mod_cast hcard_two
  have hT : 0 < (horizon : Real) := by exact_mod_cast hhorizon_pos
  have hgamma_pos :=
    tunedExplorationRate_pos (arms.card : Real) (horizon : Real) hK_one hT
  have hgamma_half :=
    tunedExplorationRate_le_half (arms.card : Real) (horizon : Real)
      hT hscale
  have hbudget :
      (arms.card : Real) * Real.log arms.card <=
        tunedExplorationRate (arms.card : Real) (horizon : Real) ^ 2 *
          (horizon : Real) := by
    rw [tunedExplorationRate_sq_mul_eq (arms.card : Real) (horizon : Real)
      hK_one hT]
  have hbound :=
    sampledPredictable_expectedRegret_le_four_mul_gamma_mul_horizon
      prior arms harms
        (tunedExplorationRate (arms.card : Real) (horizon : Real))
        hgamma_pos hgamma_half loss horizon hbudget comparator hcomparator
  dsimp only [tunedLearningRate] at hbound ⊢
  have hnormalized :
      integral
        (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
          (tunedExplorationRate (arms.card : Real) (horizon : Real) /
            (arms.card : Real))
          (tunedExplorationRate (arms.card : Real) (horizon : Real))
          hgamma_pos.le (hgamma_half.trans (by norm_num)) loss.environment)
        (fun sample =>
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt arms
                (tunedExplorationRate (arms.card : Real) (horizon : Real) /
                  (arms.card : Real))
                (tunedExplorationRate (arms.card : Real) (horizon : Real))
                loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)) <=
        4 * Real.sqrt
          ((arms.card : Real) * (horizon : Real) * Real.log arms.card) := by
    calc
      _ <= 4 * tunedExplorationRate (arms.card : Real) (horizon : Real) *
          (horizon : Real) := hbound
      _ = 4 * Real.sqrt
          ((arms.card : Real) * (horizon : Real) * Real.log arms.card) := by
        rw [mul_assoc, tunedExplorationRate_mul_eq_sqrt_mul
          (arms.card : Real) (horizon : Real) hK_one hT]
  simpa only [tunedPredictableTrajectoryKernel] using hnormalized

end Exp3
end BanditRLProof
