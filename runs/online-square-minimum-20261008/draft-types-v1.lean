import BanditRLProof.OnlineLearningFTL
import BanditRLProof.OnlineLearningRegret
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace BanditRL.OnlineLearning
noncomputable def squaredBestRegret (y prediction : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, (prediction t - y t)^2) -
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) ''
      Set.Icc (0 : ℝ) 1)

end BanditRL.OnlineLearning

open BanditRL.OnlineLearning
namespace DraftMinimum
def Q001 : Prop := ∀ (y : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    empiricalMean y T ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (∑ t ∈ Finset.range T, (empiricalMean y T - y t)^2) ≤
          ∑ t ∈ Finset.range T, (u - y t)^2

def Q002 : Prop := ∀ (y : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) ''
      Set.Icc (0 : ℝ) 1) =
        ∑ t ∈ Finset.range T, (empiricalMean y T - y t)^2

def Q003 : Prop := ∀ (y prediction : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    squaredBestRegret y prediction T =
      comparatorRegret (fun t x => (x - y t)^2) prediction (empiricalMean y T) T

def Q004 : Prop := ∀ (y prediction : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1),
    comparatorRegret (fun t x => (x - y t)^2) prediction u T ≤
      squaredBestRegret y prediction T

def Q005 : Prop := ∀ (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    squaredBestRegret y (meanPredict y) T ≤ 4 + 4 * Real.log T

def Q006 : Prop := ∀ (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    squaredBestRegret y (meanPredict y) T ≤
      (1 : ℝ) / 4 + ∑ t ∈ Finset.range (T - 1), 4 / ((t : ℝ) + 2)

end DraftMinimum

#check IsLeast.csInf_eq
#check csInf_le
#check le_csInf
#check BanditRL.OnlineLearning.empiricalMean_mem
#check BanditRL.OnlineLearning.empiricalMean_minimizes
#check BanditRL.OnlineLearning.theorem_1_3
#check BanditRL.OnlineLearning.meanPredict_regret_refined
#check BanditRL.OnlineLearning.lemma_1_2
