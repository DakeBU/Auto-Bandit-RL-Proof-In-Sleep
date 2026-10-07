import Tests.OnlineLearningFTLStateCanary
import BanditRLProof.OnlineLearningFTLState
import Mathlib.Tactic
namespace Neutral
noncomputable def a (y : ℕ → ℝ) (n : ℕ) : ℝ := (∑ t ∈ Finset.range n, y t) / n
noncomputable def b (initial : ℝ) (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then initial else a y t
noncomputable def c (state : ℕ × ℝ) (target : ℝ) : ℕ × ℝ :=
  (state.1 + 1, state.2 + (target - state.2) / ((state.1 : ℝ) + 1))
noncomputable def d (initial : ℝ) (y : ℕ → ℝ) : ℕ → ℕ × ℝ
  | 0 => (0, initial)
  | t + 1 => c (d initial y t) (y t)
noncomputable def e (y : ℕ → ℝ) (t : ℕ) : ℝ := if t = 0 then 1/2 else a y t
def f (t : ℕ) : ℝ := if t = 0 then 0 else 1
def N01 : Prop :=
    ∀ (y : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (u : ℝ),
    (∑ t ∈ Finset.range n, (u - y t)^2) =
      (∑ t ∈ Finset.range n, (a y n - y t)^2) +
        n * (u - a y n)^2

def N02 : Prop :=
    ∀ (y : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (u : ℝ),
    (∑ t ∈ Finset.range n, (a y n - y t)^2) ≤
      ∑ t ∈ Finset.range n, (u - y t)^2

def N03 : Prop :=
    ∀ (y : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hy : ∀ t < n, y t ∈ Set.Icc (0 : ℝ) 1),
    a y n ∈ Set.Icc (0 : ℝ) 1

def N04 : Prop :=
    ∀ (y : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (u : ℝ)
    (hu : (∑ t ∈ Finset.range n, (u-y t)^2) ≤
      ∑ t ∈ Finset.range n, (a y n-y t)^2),
    u = a y n

def N05 : Prop :=
    ∀ (y : ℕ → ℝ) (t : ℕ),
    a y (t + 1) = a y t +
      (y t - a y t) / ((t : ℝ) + 1)

def N06 : Prop :=
    ∀ (initial : ℝ) (y z : ℕ → ℝ) (t : ℕ)
    (h : ∀ i < t, y i = z i),
    b initial y t = b initial z t

def N07 : Prop :=
    ∀ (initial : ℝ) (y : ℕ → ℝ) (t : ℕ)
    (hi : initial ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ i < t, y i ∈ Set.Icc (0 : ℝ) 1),
    b initial y t ∈ Set.Icc (0 : ℝ) 1

def N08 : Prop :=
    ∀ (y : ℕ → ℝ) (t : ℕ),
    b ((1 : ℝ) / 2) y t = e y t

def N09 : Prop :=
    ∀ (initial : ℝ) (y : ℕ → ℝ),
    d initial y 1 = (1, y 0)

def N10 : Prop :=
    ∀ (initial : ℝ) (y : ℕ → ℝ) (t : ℕ),
    d initial y t = (t, b initial y t)

def N11 : Prop :=
    ∀ (initial : ℝ) (y z : ℕ → ℝ) (t : ℕ)
    (h : ∀ i < t, y i = z i),
    d initial y t = d initial z t

def N12 : Prop :=
    ∀ (initial : ℝ) (y : ℕ → ℝ) (t : ℕ)
    (hi : initial ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ i < t, y i ∈ Set.Icc (0 : ℝ) 1),
    (d initial y t).2 ∈ Set.Icc (0 : ℝ) 1

def N13 : Prop :=
    ∀ (y : ℕ → ℝ) (t : ℕ),
    d ((1 : ℝ) / 2) y t = (t, e y t)

def N14 : Prop :=
    d 0 (fun _ => 1) 0 = (0, 0) ∧
    d 1 (fun _ => 1) 0 = (0, 1) ∧
    d 0 (fun _ => 1) 1 = (1, 1) ∧
    d 1 (fun _ => 1) 1 = (1, 1)

def N15 : Prop :=
    d ((3 : ℝ) / 4) f 2 = (2, (1 : ℝ) / 2) ∧
    d ((3 : ℝ) / 4) f 3 = (3, (2 : ℝ) / 3)

def N16 : Prop :=
    d 0 (fun _ => 0) 1 = d 0 f 1 ∧
    (0 : ℝ) ≠ f 1 ∧
    d 0 (fun _ => 0) 2 ≠ d 0 f 2

def N17 : Prop :=
    (d 1 f 2).2 ∈ Set.Icc (0 : ℝ) 1 ∧
    (d 2 f 0).2 ∉ Set.Icc (0 : ℝ) 1 ∧
    (d 2 f 1).2 = 0

def N18 : Prop :=
    ((∑ t ∈ Finset.range 2, ((d ((1 : ℝ) / 2) f t).2 - f t)^2) -
      (∑ t ∈ Finset.range 2, (a f 2 - f t)^2)) = (3 : ℝ) / 4 ∧
    ((∑ t ∈ Finset.range 2, ((d ((1 : ℝ) / 2) f t).2 - f t)^2) -
      (∑ t ∈ Finset.range 2, (a f 2 - f t)^2)) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range (2 - 1), 4 / ((t : ℝ) + 2)

def N19 : Prop :=
    (d 1 (fun _ => 0) 0).2 ∈ Set.Icc (0 : ℝ) 1 ∧
    ((d 1 (fun _ => 0) 0).2 - 0)^2 = 1 ∧
    ((d 1 (fun _ => 0) 0).2 - 0)^2 > (1 : ℝ) / 4
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
#check N14
#check N15
#check N16
#check N17
#check N18
#check N19
end Neutral

example : Neutral.a = BanditRL.OnlineLearning.empiricalMean := by rfl
example : Neutral.b = BanditRL.OnlineLearning.ftlPredict := by rfl
example : Neutral.c = BanditRL.OnlineLearning.ftlMeanStep := by rfl
theorem neutralStateIdentity : Neutral.d = BanditRL.OnlineLearning.ftlState := by
  funext initial y t
  induction t with
  | zero => rfl
  | succ t ih =>
    change Neutral.c (Neutral.d initial y t) (y t) =
      BanditRL.OnlineLearning.ftlMeanStep (BanditRL.OnlineLearning.ftlState initial y t) (y t)
    rw [ih]
    rfl
#check BanditRL.OnlineLearning.ftlPredict
#print axioms BanditRL.OnlineLearning.ftlPredict
#check BanditRL.OnlineLearning.ftlMeanStep
#print axioms BanditRL.OnlineLearning.ftlMeanStep
#check BanditRL.OnlineLearning.ftlState
#print axioms BanditRL.OnlineLearning.ftlState

def propositionOf {P : Prop} (_ : P) : Prop := P
example : Neutral.f = FTLStateProbe.probeTargets := by rfl
example : Neutral.e = BanditRL.OnlineLearning.meanPredict := by rfl
example : Neutral.N01 = propositionOf (@BanditRL.OnlineLearning.empiricalMean_decomposition) := by
  unfold Neutral.N01 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N02 = propositionOf (@BanditRL.OnlineLearning.empiricalMean_minimizes) := by
  unfold Neutral.N02 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N03 = propositionOf (@BanditRL.OnlineLearning.empiricalMean_mem) := by
  unfold Neutral.N03 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N04 = propositionOf (@BanditRL.OnlineLearning.empiricalMean_unique) := by
  unfold Neutral.N04 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N05 = propositionOf (@BanditRL.OnlineLearning.empiricalMean_succ) := by
  unfold Neutral.N05 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N06 = propositionOf (@BanditRL.OnlineLearning.ftlPredict_prefix) := by
  unfold Neutral.N06 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N07 = propositionOf (@BanditRL.OnlineLearning.ftlPredict_mem) := by
  unfold Neutral.N07 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N08 = propositionOf (@BanditRL.OnlineLearning.ftlPredict_half) := by
  unfold Neutral.N08 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N09 = propositionOf (@BanditRL.OnlineLearning.ftlState_first) := by
  unfold Neutral.N09 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N10 = propositionOf (@BanditRL.OnlineLearning.ftlState_eq_predict) := by
  unfold Neutral.N10 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N11 = propositionOf (@BanditRL.OnlineLearning.ftlState_prefix) := by
  unfold Neutral.N11 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N12 = propositionOf (@BanditRL.OnlineLearning.ftlState_mem) := by
  unfold Neutral.N12 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N13 = propositionOf (@BanditRL.OnlineLearning.ftlState_half) := by
  unfold Neutral.N13 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N14 = propositionOf (@FTLStateProbe.initial_and_first) := by
  unfold Neutral.N14 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N15 = propositionOf (@FTLStateProbe.varying_updates) := by
  unfold Neutral.N15 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N16 = propositionOf (@FTLStateProbe.current_target_after_prediction) := by
  unfold Neutral.N16 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N17 = propositionOf (@FTLStateProbe.feasibility_and_outside) := by
  unfold Neutral.N17 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N18 = propositionOf (@FTLStateProbe.half_state_regret) := by
  unfold Neutral.N18 propositionOf
  try rw [neutralStateIdentity]
  rfl
example : Neutral.N19 = propositionOf (@FTLStateProbe.general_initial_not_quarter) := by
  unfold Neutral.N19 propositionOf
  try rw [neutralStateIdentity]
  rfl
