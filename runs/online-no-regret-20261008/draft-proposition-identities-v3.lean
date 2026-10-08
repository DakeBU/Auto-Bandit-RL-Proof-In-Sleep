import BanditRLProof.OnlineLearningAsymptotic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas


open Filter
namespace BanditRL.OnlineLearning

/-- Literal ordinary-real-limit reading, kept separate from the shared upper condition. -/
def LimitNoRegret {X : Type*} (V : Set X) (loss : ℕ → X → ℝ)
    (prediction : ℕ → X) : Prop :=
  ∀ u ∈ V, ∃ a : ℝ, a ≤ 0 ∧
    Tendsto (fun T : ℕ => comparatorRegret loss prediction u T / T) atTop (nhds a)

namespace NoRegretCounterexample

/-- A nonnegative horizon potential with alternating normalized values. -/
noncomputable def potential (T : ℕ) : ℝ :=
  if T % 2 = 0 then (T : ℝ) else 0

/-- Actual exogenous real affine losses; no horizon-dependent learner. -/
noncomputable def loss (t : ℕ) (x : ℝ) : ℝ :=
  (potential (t + 1) - potential t) * x

end NoRegretCounterexample
end BanditRL.OnlineLearning

open Filter
universe v
namespace NeutralPacket
noncomputable def r {X : Type v} (f : ℕ → X → ℝ) (p : ℕ → X) (u : X) (N : ℕ) : ℝ :=
  (∑ t ∈ Finset.range N, f t (p t)) - ∑ t ∈ Finset.range N, f t u
def upper {X : Type v} (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X) : Prop :=
  ∀ u ∈ V, ∀ e : ℝ, 0 < e → ∀ᶠ N in atTop, r f p u N / N ≤ e
def limit {X : Type v} (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X) : Prop :=
  ∀ u ∈ V, ∃ a : ℝ, a ≤ 0 ∧ Tendsto (fun N : ℕ => r f p u N / N) atTop (nhds a)
noncomputable def h (N : ℕ) : ℝ := if N % 2 = 0 then (N : ℝ) else 0
noncomputable def f (t : ℕ) (x : ℝ) : ℝ := (h (t+1) - h t) * x
noncomputable def q (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 1/2 else (∑ i ∈ Finset.range t, y i) / t
def B001 : Prop := ∀ (X : Type v) (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X),
  upper V f p → ∀ u ∈ V, ∀ a : ℝ,
    Tendsto (fun N : ℕ => r f p u N / N) atTop (nhds a) → a ≤ 0
def B002 : Prop := ∀ (X : Type v) (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X),
  limit V f p → upper V f p
def B003 : Prop := ∀ (X : Type v) (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X),
  (∀ u ∈ V, ∃ a : ℝ, Tendsto (fun N : ℕ => r f p u N / N) atTop (nhds a)) →
    (limit V f p ↔ upper V f p)
def B004 : Prop := ∀ (N : ℕ) (u : ℝ), r f (fun _ => 0) u N = -h N * u
def B005 : Prop := upper (Set.Icc (0 : ℝ) 1) f (fun _ => 0)
def B006 : Prop := ∀ n : ℕ, r f (fun _ => 0) 1 (2*(n+1)) / ((2*(n+1) : ℕ) : ℝ) = -1
def B007 : Prop := ∀ n : ℕ, r f (fun _ => 0) 1 (2*n+1) / ((2*n+1 : ℕ) : ℝ) = 0
def B008 : Prop := ¬ ∃ a : ℝ, Tendsto (fun N : ℕ => r f (fun _ => 0) 1 N / N) atTop (nhds a)
def B009 : Prop := upper (Set.Icc (0 : ℝ) 1) f (fun _ => 0) ∧ ¬ limit (Set.Icc (0 : ℝ) 1) f (fun _ => 0)
def B010 : Prop := ∀ y : ℕ → ℝ, (∀ t, y t ∈ Set.Icc (0 : ℝ) 1) →
  upper (Set.Icc (0 : ℝ) 1) (fun t x => (x-y t)^2) (q y)
def B011 : Prop := ∀ (X : Type v) (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X) (b : X → ℕ → ℝ),
  (∀ u ∈ V, ∀ᶠ N in atTop, r f p u N / N ≤ b u N) →
  (∀ u ∈ V, Tendsto (b u) atTop (nhds 0)) → upper V f p
def B012 : Prop := ∀ (X : Type v) (f : ℕ → X → ℝ) (p : ℕ → X) (u : X) (N : ℕ),
  r f p u N = ∑ t ∈ Finset.range N, (f t (p t) - f t u)
end NeutralPacket

open BanditRL.OnlineLearning
namespace DraftTypeVerification

def A001 : Prop := ∀ {X : Type v} (V : Set X)
    (loss : ℕ → X → ℝ) (prediction : ℕ → X)
    (hNR : NoRegret V loss prediction) (u : X) (hu : u ∈ V) (a : ℝ)
    (hl : Tendsto (fun T : ℕ => comparatorRegret loss prediction u T / T) atTop (nhds a)),
a ≤ 0

example : NeutralPacket.B001 = A001 := by
  apply propext
  constructor
  · intro h X V f p
    exact h X V f p
  · intro h X V f p
    exact @h X V f p

def A002 : Prop := ∀ {X : Type v} (V : Set X)
    (loss : ℕ → X → ℝ) (prediction : ℕ → X)
    (hL : LimitNoRegret V loss prediction),
NoRegret V loss prediction

example : NeutralPacket.B002 = A002 := by
  apply propext
  constructor
  · intro h X V f p
    exact h X V f p
  · intro h X V f p
    exact @h X V f p

def A003 : Prop := ∀ {X : Type v} (V : Set X)
    (loss : ℕ → X → ℝ) (prediction : ℕ → X)
    (hc : ∀ u ∈ V, ∃ a : ℝ,
      Tendsto (fun T : ℕ => comparatorRegret loss prediction u T / T) atTop (nhds a)),
LimitNoRegret V loss prediction ↔ NoRegret V loss prediction

example : NeutralPacket.B003 = A003 := by
  apply propext
  constructor
  · intro h X V f p
    exact h X V f p
  · intro h X V f p
    exact @h X V f p

open NoRegretCounterexample
def A004 : Prop := ∀ (T : ℕ) (u : ℝ),
comparatorRegret loss (fun _ => 0) u T = -potential T * u

example : NeutralPacket.B004 = A004 := by rfl

def A005 : Prop := NoRegret (Set.Icc (0 : ℝ) 1) loss (fun _ => 0)

example : NeutralPacket.B005 = A005 := by rfl

def A006 : Prop := ∀ (n : ℕ),
comparatorRegret loss (fun _ => 0) 1 (2 * (n + 1)) /
      ((2 * (n + 1) : ℕ) : ℝ) = -1

example : NeutralPacket.B006 = A006 := by rfl

def A007 : Prop := ∀ (n : ℕ),
comparatorRegret loss (fun _ => 0) 1 (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℝ) = 0

example : NeutralPacket.B007 = A007 := by rfl

def A008 : Prop := ¬ ∃ a : ℝ, Tendsto
      (fun T : ℕ => comparatorRegret loss (fun _ => 0) 1 T / T) atTop (nhds a)

example : NeutralPacket.B008 = A008 := by rfl

def A009 : Prop := NoRegret (Set.Icc (0 : ℝ) 1) loss (fun _ => 0) ∧
      ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) loss (fun _ => 0)

example : NeutralPacket.B009 = A009 := by rfl

def A010 : Prop := ∀ y : ℕ → ℝ, (∀ t, y t ∈ Set.Icc (0 : ℝ) 1) →
  NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x-y t)^2) (meanPredict y)
example : NeutralPacket.B010 = A010 := by rfl
def A011 : Prop := ∀ (X : Type v) (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X) (b : X → ℕ → ℝ),
  (∀ u ∈ V, ∀ᶠ N in atTop, comparatorRegret f p u N / N ≤ b u N) →
  (∀ u ∈ V, Tendsto (b u) atTop (nhds 0)) → NoRegret V f p
example : NeutralPacket.B011 = A011 := by rfl
def A012 : Prop := ∀ (X : Type v) (f : ℕ → X → ℝ) (p : ℕ → X) (u : X) (N : ℕ),
  comparatorRegret f p u N = ∑ t ∈ Finset.range N, (f t (p t) - f t u)
example : NeutralPacket.B012 = A012 := by rfl
end DraftTypeVerification
