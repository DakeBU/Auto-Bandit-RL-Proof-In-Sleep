import BanditRLProof.OnlineLearningFTL
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
namespace Neutral
noncomputable def a (y : ℕ → ℝ) (n : ℕ) : ℝ := (∑ t ∈ Finset.range n, y t) / n
noncomputable def b (y : ℕ → ℝ) (t : ℕ) : ℝ := if t = 0 then 1/2 else a y t
def c (t : ℕ) : ℝ := if t = 0 then 0 else 1
def N01 : Prop :=
    ∀ (y z : ℕ → ℝ) (t : ℕ) (h : ∀ i < t, y i = z i),
    b y t = b z t

def N02 : Prop :=
    ∀ (y : ℕ → ℝ) (t : ℕ)
    (hy : ∀ i < t, y i ∈ Set.Icc (0 : ℝ) 1),
    b y t ∈ Set.Icc (0 : ℝ) 1

def N03 : Prop :=
    ∀ (y : ℕ → ℝ) (t : ℕ) (ht : 0 < t),
    a y (t+1) = a y t +
      (y t - a y t) / (t+1)

def N04 : Prop :=
    ∀ (y : ℕ → ℝ) (t : ℕ)
    (hy : ∀ i ≤ t, y i ∈ Set.Icc (0 : ℝ) 1),
    (b y t - y t)^2 - (a y (t+1) - y t)^2 ≤
      4 / (t+1)

def N05 : Prop :=
    ∀ (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    (∑ t ∈ Finset.range T, (b y t - y t)^2) -
      (∑ t ∈ Finset.range T, (a y T - y t)^2) ≤
        4 + 4 * Real.log T

def N06 : Prop :=
    ∀ (y : ℕ → ℝ)
    (hy : y 0 ∈ Set.Icc (0 : ℝ) 1),
    (b y 0 - y 0)^2 - (a y 1 - y 0)^2 ≤ (1 : ℝ) / 4

def N07 : Prop :=
    ∀ (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    (∑ t ∈ Finset.range T, (b y t - y t)^2) -
      (∑ t ∈ Finset.range T, (a y T - y t)^2) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range (T - 1), 4 / ((t : ℝ) + 2)

def N08 : Prop :=
    (b (fun _ => 0) 0 - 0)^2 - (a (fun _ => 0) 1 - 0)^2 = (1 : ℝ) / 4 ∧
    (b (fun _ => 1) 0 - 1)^2 - (a (fun _ => 1) 1 - 1)^2 = (1 : ℝ) / 4 ∧
    (b (fun _ => 0) 0 - 0)^2 - (a (fun _ => 0) 1 - 0)^2 ≤ (1 : ℝ) / 4 ∧
    (b (fun _ => 1) 0 - 1)^2 - (a (fun _ => 1) 1 - 1)^2 ≤ (1 : ℝ) / 4

def N09 : Prop :=
    (b (fun _ => (1 : ℝ) / 2) 0 - 1 / 2)^2 -
      (a (fun _ => (1 : ℝ) / 2) 1 - 1 / 2)^2 = 0 ∧
    (b (fun _ => (1 : ℝ) / 2) 0 - 1 / 2)^2 -
      (a (fun _ => (1 : ℝ) / 2) 1 - 1 / 2)^2 < (1 : ℝ) / 4

def N10 : Prop :=
    (b (fun _ => 2) 0 - 2)^2 - (a (fun _ => 2) 1 - 2)^2 = (9 : ℝ) / 4 ∧
    (b (fun _ => 2) 0 - 2)^2 - (a (fun _ => 2) 1 - 2)^2 > (1 : ℝ) / 4

def N11 : Prop :=
    ((∑ t ∈ Finset.range 1, (b (fun _ => 0) t - 0)^2) -
      (∑ t ∈ Finset.range 1, (a (fun _ => 0) 1 - 0)^2) = (1 : ℝ) / 4) ∧
    ((∑ t ∈ Finset.range 1, (b (fun _ => 0) t - 0)^2) -
      (∑ t ∈ Finset.range 1, (a (fun _ => 0) 1 - 0)^2) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range (1 - 1), 4 / ((t : ℝ) + 2))

def N12 : Prop :=
    ((∑ t ∈ Finset.range 2, (b c t - c t)^2) -
      (∑ t ∈ Finset.range 2, (a c 2 - c t)^2) = (3 : ℝ) / 4) ∧
    ((∑ t ∈ Finset.range 2, (b c t - c t)^2) -
      (∑ t ∈ Finset.range 2, (a c 2 - c t)^2) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range (2 - 1), 4 / ((t : ℝ) + 2)) ∧
    ((1 : ℝ) / 4 + ∑ t ∈ Finset.range (2 - 1), 4 / ((t : ℝ) + 2)) = 9 / 4

def N13 : Prop :=
    b (fun _ => 0) 1 = b c 1 ∧
    (0 : ℝ) ≠ c 1
#check N01
#check N02
#check N03
#check N04
#check N05
#check N06
#check N07
#check N08
#check N09
#check N10
#check N11
#check N12
#check N13
#check Finset.sum_range_succ'
end Neutral

def propositionOf {P : Prop} (_ : P) : Prop := P
example : Neutral.N06 = propositionOf (@BanditRL.OnlineLearning.meanPredict_initial_stability) := by rfl
#check BanditRL.OnlineLearning.meanPredict_initial_stability
#print axioms BanditRL.OnlineLearning.meanPredict_initial_stability
open BanditRL.OnlineLearning
example : (meanPredict (fun _ => 0) 0 - 0)^2 - (empiricalMean (fun _ => 0) 1 - 0)^2 ≤ (1 : ℝ) / 4 :=
  meanPredict_initial_stability _ (by norm_num)
example : (meanPredict (fun _ => 1) 0 - 1)^2 - (empiricalMean (fun _ => 1) 1 - 1)^2 ≤ (1 : ℝ) / 4 :=
  meanPredict_initial_stability _ (by norm_num)
example : (meanPredict (fun _ => (1:ℝ)/2) 0 - 1/2)^2 - (empiricalMean (fun _ => (1:ℝ)/2) 1 - 1/2)^2 = 0 := by
  norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
example : (meanPredict (fun _ => 2) 0 - 2)^2 - (empiricalMean (fun _ => 2) 1 - 2)^2 > (1:ℝ)/4 := by
  norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
