import BanditRLProof.LowerBounds.SubgaussianMinimax

open scoped ENNReal
open BanditRLProof

example {k : ℕ} [NeZero k] (hk : 1 < k) (t : ℕ) (hkt : k ≤ t+1) :
    LowerBounds.subgaussianWorstCaseExpectedPseudoRegret k
      (MOSS.historyAlgorithm (by omega) (t+1)) t ≤
      2160 * LowerBounds.subgaussianMinimaxExpectedPseudoRegret k t :=
  LowerBounds.moss_nearMinimax hk t hkt

#print axioms LowerBounds.UnitGaussianBanditEnvironment.toSubgaussian
#print axioms LowerBounds.unitGaussianMinimax_le_subgaussianMinimax
#print axioms LowerBounds.moss_subgaussianExpectedPseudoRegret_le
#print axioms LowerBounds.subgaussianMinimax_sandwich
#print axioms LowerBounds.moss_nearMinimax
