import Tests.OnlineSquareMinimumCanary
import Mathlib
import BanditRLProof.OnlineLearningFTL
import BanditRLProof.OnlineLearningRegret
import Mathlib.Order.ConditionallyCompleteLattice.Basic


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

namespace ActualTypeVerification
def propositionOf {P : Prop} (_ : P) : Prop := P
example : DraftMinimum.Q001 = propositionOf (@BanditRL.OnlineLearning.guessing_prefix_minimum) := by rfl
example : DraftMinimum.Q002 = propositionOf (@BanditRL.OnlineLearning.squaredLoss_minimum_eq) := by rfl
example : DraftMinimum.Q003 = propositionOf (@BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret) := by rfl
example : DraftMinimum.Q004 = propositionOf (@BanditRL.OnlineLearning.comparatorRegret_le_squaredBestRegret) := by rfl
example : DraftMinimum.Q005 = propositionOf (@BanditRL.OnlineLearning.meanPredict_bestRegret_bound) := by rfl
example : DraftMinimum.Q006 = propositionOf (@BanditRL.OnlineLearning.meanPredict_bestRegret_refined) := by rfl
open Tests.OnlineSquareMinimum

def C001 : Prop := ∀ (t : ℕ),
alternating t ∈ Set.Icc (0 : ℝ) 1
example : C001 = propositionOf (@Tests.OnlineSquareMinimum.alternating_mem) := by rfl

def C002 : Prop := ∀ (t : ℕ),
quarters t ∈ Set.Icc (0 : ℝ) 1
example : C002 = propositionOf (@Tests.OnlineSquareMinimum.quarters_mem) := by rfl

def C003 : Prop := sInf ((fun u : ℝ => ∑ t ∈ Finset.range 0, (u - alternating t)^2) ''
      Set.Icc (0 : ℝ) 1) = 0
example : C003 = propositionOf (@Tests.OnlineSquareMinimum.empty_minimum) := by rfl

def C004 : Prop := squaredBestRegret alternating (meanPredict alternating) 0 = 0
example : C004 = propositionOf (@Tests.OnlineSquareMinimum.empty_regret) := by rfl

def C005 : Prop := empiricalMean alternating 2 = 1 / 2
example : C005 = propositionOf (@Tests.OnlineSquareMinimum.alternating_mean) := by rfl

def C006 : Prop := sInf ((fun u : ℝ => ∑ t ∈ Finset.range 2, (u - alternating t)^2) ''
      Set.Icc (0 : ℝ) 1) = 1 / 2
example : C006 = propositionOf (@Tests.OnlineSquareMinimum.alternating_minimum) := by rfl

def C007 : Prop := ∀ (u : ℝ)
    (hu : (∑ t ∈ Finset.range 2, (u - alternating t)^2) ≤
      ∑ t ∈ Finset.range 2, (empiricalMean alternating 2 - alternating t)^2),
u = 1 / 2
example : C007 = propositionOf (@Tests.OnlineSquareMinimum.alternating_unique) := by rfl

def C008 : Prop := meanPredict alternating 0 = 1 / 2 ∧ meanPredict alternating 1 = 0 ∧
      meanPredict alternating 2 = 1 / 2
example : C008 = propositionOf (@Tests.OnlineSquareMinimum.actual_prediction_values) := by rfl

def C009 : Prop := squaredBestRegret alternating (meanPredict alternating) 1 = 1 / 4
example : C009 = propositionOf (@Tests.OnlineSquareMinimum.actual_regret_one) := by rfl

def C010 : Prop := squaredBestRegret alternating (meanPredict alternating) 2 = 3 / 4
example : C010 = propositionOf (@Tests.OnlineSquareMinimum.actual_regret_two) := by rfl

def C011 : Prop := squaredBestRegret alternating alternating 2 = -1 / 2
example : C011 = propositionOf (@Tests.OnlineSquareMinimum.signed_alternating) := by rfl

def C012 : Prop := comparatorRegret (fun t x => (x - alternating t)^2) (meanPredict alternating) 0 2 ≤
      squaredBestRegret alternating (meanPredict alternating) 2
example : C012 = propositionOf (@Tests.OnlineSquareMinimum.comparator_zero_order) := by rfl

def C013 : Prop := comparatorRegret (fun t x => (x - alternating t)^2) (meanPredict alternating) 1 2 ≤
      squaredBestRegret alternating (meanPredict alternating) 2
example : C013 = propositionOf (@Tests.OnlineSquareMinimum.comparator_one_order) := by rfl

def C014 : Prop := empiricalMean quarters 2 = 1 / 2
example : C014 = propositionOf (@Tests.OnlineSquareMinimum.quarters_mean) := by rfl

def C015 : Prop := sInf ((fun u : ℝ => ∑ t ∈ Finset.range 2, (u - quarters t)^2) ''
      Set.Icc (0 : ℝ) 1) = 1 / 8
example : C015 = propositionOf (@Tests.OnlineSquareMinimum.quarters_minimum) := by rfl

def C016 : Prop := squaredBestRegret alternating (meanPredict alternating) 2 ≤ 4 + 4 * Real.log 2
example : C016 = propositionOf (@Tests.OnlineSquareMinimum.actual_bound) := by rfl

def C017 : Prop := squaredBestRegret alternating (meanPredict alternating) 2 ≤ 9 / 4
example : C017 = propositionOf (@Tests.OnlineSquareMinimum.actual_refined) := by rfl

def C018 : Prop := squaredBestRegret alternating (meanPredict alternating) 1 ≤ 1 / 4
example : C018 = propositionOf (@Tests.OnlineSquareMinimum.actual_refined_one) := by rfl

def C019 : Prop := ∀ (y z : ℕ → ℝ) (t : ℕ) (h : ∀ i < t, y i = z i),
meanPredict y t = meanPredict z t
example : C019 = propositionOf (@Tests.OnlineSquareMinimum.actual_causality) := by rfl

def C020 : Prop := squaredBestRegret alternating (meanPredict alternating) 2 =
      comparatorRegret (fun t x => (x - alternating t)^2) (meanPredict alternating) (1 / 2) 2
example : C020 = propositionOf (@Tests.OnlineSquareMinimum.actual_identity) := by rfl

noncomputable def alternatingFixture (t : ℕ) : ℝ := if t % 2 = 0 then 0 else 1
noncomputable def quartersFixture (t : ℕ) : ℝ := if t % 2 = 0 then 1 / 4 else 3 / 4
example : alternatingFixture = Tests.OnlineSquareMinimum.alternating := by rfl
example : quartersFixture = Tests.OnlineSquareMinimum.quarters := by rfl
end ActualTypeVerification
