import BanditRLProof.Algorithms.MOSSHistoryRegret
import BanditRLProof.LowerBounds.GaussianHypothesisTesting

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BanditRLProof.LowerBounds

/-- The class in Chapter 13's main prose: gaps, not means, lie in [0,1]. -/
structure UnitSubgaussianBanditEnvironment (k : ℕ) where
  armLaw : Kernel (Fin k) ℝ
  markov : IsMarkovKernel armLaw
  mean : Fin k → ℝ
  bestArm : Fin k
  mean_eq : ∀ a, ∫ r, r ∂armLaw a = mean a
  subgaussian : ∀ a, HasSubgaussianMGF (fun r => r-mean a) 1 (armLaw a)
  isBest : ∀ a, mean a ≤ mean bestArm
  gap_le_one : ∀ a, mean bestArm-mean a ≤ 1

attribute [instance] UnitSubgaussianBanditEnvironment.markov

def UnitGaussianBanditEnvironment.toSubgaussian {k : ℕ}
    (e : UnitGaussianBanditEnvironment k) : UnitSubgaussianBanditEnvironment k where
  armLaw := unitGaussianKernel e.mean
  markov := inferInstance
  mean := e.mean
  bestArm := e.bestArm
  mean_eq := fun a => integral_id_gaussianReal
  subgaussian := by
    intro a
    have h := (hasSubgaussianMGF_gap_sub_id_gaussianReal (e.mean a) 1).neg
    change HasSubgaussianMGF (fun r => -(e.mean a-r)) 1 (gaussianReal (e.mean a) 1) at h
    simpa only [neg_sub] using h
  isBest := e.isBest
  gap_le_one := fun a => sub_le_iff_le_add.mpr
    ((e.mean_mem_unit e.bestArm).2.trans (le_add_of_nonneg_right (e.mean_mem_unit a).1))

def subgaussianExpectedPseudoRegret {k : ℕ}
    (algorithm : Thompson.HistoryAlgorithm (Fin k) ℝ)
    (e : UnitSubgaussianBanditEnvironment k) (t : ℕ) : ℝ≥0∞ :=
  canonicalGapExpectedPseudoRegret algorithm e.armLaw (fun a => e.mean e.bestArm-e.mean a) t

def subgaussianWorstCaseExpectedPseudoRegret (k : ℕ)
    (algorithm : Thompson.HistoryAlgorithm (Fin k) ℝ) (t : ℕ) : ℝ≥0∞ :=
  ⨆ e : UnitSubgaussianBanditEnvironment k, subgaussianExpectedPseudoRegret algorithm e t

def subgaussianMinimaxExpectedPseudoRegret (k t : ℕ) : ℝ≥0∞ :=
  ⨅ algorithm : Thompson.HistoryAlgorithm (Fin k) ℝ,
    subgaussianWorstCaseExpectedPseudoRegret k algorithm t

theorem subgaussianExpectedPseudoRegret_gaussian {k : ℕ}
    (algorithm : Thompson.HistoryAlgorithm (Fin k) ℝ)
    (e : UnitGaussianBanditEnvironment k) (t : ℕ) :
    subgaussianExpectedPseudoRegret algorithm e.toSubgaussian t =
      gaussianExpectedPseudoRegret algorithm e t := rfl

/-- Gaussian subclass inclusion is on the identical policy and regret functional. -/
theorem unitGaussianMinimax_le_subgaussianMinimax (k t : ℕ) :
    unitGaussianMinimaxExpectedPseudoRegret k t ≤ subgaussianMinimaxExpectedPseudoRegret k t := by
  apply iInf_mono
  intro algorithm
  apply iSup_le
  intro e
  exact (subgaussianExpectedPseudoRegret_gaussian algorithm e t).symm.le.trans
    (le_iSup (fun e => subgaussianExpectedPseudoRegret algorithm e t) e.toSubgaussian)

theorem moss_subgaussianExpectedPseudoRegret_le {k : ℕ} [NeZero k]
    (hk : 0 < k) (t : ℕ) (hkt : k ≤ t+1) (e : UnitSubgaussianBanditEnvironment k) :
    subgaussianExpectedPseudoRegret (MOSS.historyAlgorithm hk (t+1)) e t ≤
      ENNReal.ofReal (40*Real.sqrt ((k : ℝ)*(t+1))) := by
  have hu := MOSS.canonicalGapExpectedRegret_le hk e.armLaw t hkt e.mean e.bestArm
    e.isBest e.mean_eq e.subgaussian
  have hg : ∑ a, (e.mean e.bestArm-e.mean a) ≤ (k : ℝ) := by
    calc
      _ ≤ ∑ _a : Fin k, (1 : ℝ) := Finset.sum_le_sum (fun a _ => e.gap_le_one a)
      _ = _ := by simp
  have hc : (k : ℝ) ≤ Real.sqrt ((k : ℝ)*(t+1)) := by
    apply Real.le_sqrt_of_sq_le
    have ht : (k : ℝ) ≤ (t : ℝ)+1 := by exact_mod_cast hkt
    nlinarith [show (0 : ℝ) ≤ k by positivity]
  have hr : (subgaussianExpectedPseudoRegret (MOSS.historyAlgorithm hk (t+1)) e t).toReal ≤
      40*Real.sqrt ((k : ℝ)*(t+1)) := by
    change (canonicalGapExpectedPseudoRegret _ _ _ _).toReal ≤ _
    dsimp [canonicalGapExpectedPseudoRegretReal] at hu
    simp only [Nat.cast_add, Nat.cast_one, mul_comm ((t : ℝ)+1)] at hu
    linarith
  change canonicalGapExpectedPseudoRegret _ _ _ _ ≤ _
  rw [← ENNReal.ofReal_toReal (canonicalGapExpectedPseudoRegret_ne_top _ _ _ _)]
  exact ENNReal.ofReal_le_ofReal hr

/-- Chapter 13's broader-class minimax sandwich with universal constants. -/
theorem subgaussianMinimax_sandwich {k : ℕ} [NeZero k]
    (hk : 1 < k) (t : ℕ) (hkt : k ≤ t+1) :
    ENNReal.ofReal ((1/54 : ℝ)*Real.sqrt ((k : ℝ)*(t+1))) ≤
      subgaussianMinimaxExpectedPseudoRegret k t ∧
    subgaussianMinimaxExpectedPseudoRegret k t ≤
      subgaussianWorstCaseExpectedPseudoRegret k (MOSS.historyAlgorithm (by omega) (t+1)) t ∧
    subgaussianWorstCaseExpectedPseudoRegret k (MOSS.historyAlgorithm (by omega) (t+1)) t ≤
      ENNReal.ofReal (40*Real.sqrt ((k : ℝ)*(t+1))) := by
  refine ⟨?_, iInf_le _ _, ?_⟩
  · have h := unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt hk hkt
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
    exact h.trans (unitGaussianMinimax_le_subgaussianMinimax k t)
  · exact iSup_le fun e => moss_subgaussianExpectedPseudoRegret_le (by omega) t hkt e

/-- Algorithm 7 is minimax optimal up to one universal multiplicative factor. -/
theorem moss_nearMinimax {k : ℕ} [NeZero k]
    (hk : 1 < k) (t : ℕ) (hkt : k ≤ t+1) :
    subgaussianWorstCaseExpectedPseudoRegret k (MOSS.historyAlgorithm (by omega) (t+1)) t ≤
      2160 * subgaussianMinimaxExpectedPseudoRegret k t := by
  obtain ⟨hl, _, hu⟩ := subgaussianMinimax_sandwich hk t hkt
  calc
    _ ≤ ENNReal.ofReal (40*Real.sqrt ((k : ℝ)*(t+1))) := hu
    _ = 2160 * ENNReal.ofReal ((1/54 : ℝ)*Real.sqrt ((k : ℝ)*(t+1))) := by
      rw [show 40*Real.sqrt ((k : ℝ)*(t+1)) =
        2160*((1/54 : ℝ)*Real.sqrt ((k : ℝ)*(t+1))) by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2160)]
      norm_num
    _ ≤ _ := mul_le_mul_left' hl _

end BanditRLProof.LowerBounds
