import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic
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
