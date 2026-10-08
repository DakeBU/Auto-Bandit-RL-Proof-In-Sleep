import Mathlib
import BanditRLProof.OnlineLearningFTL
import BanditRLProof.OnlineLearningRegret
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace BanditRL.OnlineLearning
noncomputable def squaredBestRegret (y prediction : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, (prediction t - y t)^2) -
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) ''
      Set.Icc (0 : ℝ) 1)

end BanditRL.OnlineLearning
namespace NeutralMinimum
noncomputable def C0 (y : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, y t) / T
noncomputable def C1 (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 1 / 2 else C0 y t
noncomputable def C2 (loss : ℕ → ℝ → ℝ) (prediction : ℕ → ℝ)
    (u : ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, loss t (prediction t)) -
    ∑ t ∈ Finset.range T, loss t u
noncomputable def C3 (y prediction : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, (prediction t - y t)^2) -
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) ''
      Set.Icc (0 : ℝ) 1)
def Q001 : Prop := ∀ (y : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    C0 y T ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (∑ t ∈ Finset.range T, (C0 y T - y t)^2) ≤
          ∑ t ∈ Finset.range T, (u - y t)^2

def Q002 : Prop := ∀ (y : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) ''
      Set.Icc (0 : ℝ) 1) =
        ∑ t ∈ Finset.range T, (C0 y T - y t)^2

def Q003 : Prop := ∀ (y prediction : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    C3 y prediction T =
      C2 (fun t x => (x - y t)^2) prediction (C0 y T) T

def Q004 : Prop := ∀ (y prediction : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1),
    C2 (fun t x => (x - y t)^2) prediction u T ≤
      C3 y prediction T

def Q005 : Prop := ∀ (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    C3 y (C1 y) T ≤ 4 + 4 * Real.log T

def Q006 : Prop := ∀ (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    C3 y (C1 y) T ≤
      (1 : ℝ) / 4 + ∑ t ∈ Finset.range (T - 1), 4 / ((t : ℝ) + 2)

end NeutralMinimum
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
example : NeutralMinimum.Q001 = DraftMinimum.Q001 := by rfl
example : NeutralMinimum.Q002 = DraftMinimum.Q002 := by rfl
example : NeutralMinimum.Q003 = DraftMinimum.Q003 := by rfl
example : NeutralMinimum.Q004 = DraftMinimum.Q004 := by rfl
example : NeutralMinimum.Q005 = DraftMinimum.Q005 := by rfl
example : NeutralMinimum.Q006 = DraftMinimum.Q006 := by rfl
example : NeutralMinimum.C0 = empiricalMean := by rfl
example : NeutralMinimum.C1 = meanPredict := by rfl
example : NeutralMinimum.C2 = comparatorRegret (X := ℝ) := by rfl
example : NeutralMinimum.C3 = squaredBestRegret := by rfl
