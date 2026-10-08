import Tests.OnlineNoRegretSemanticsCanary
import BanditRLProof.OnlineLearningAsymptotic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas




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

example : NeutralPacket.B001.{v} = A001.{v} := by
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

example : NeutralPacket.B002.{v} = A002.{v} := by
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

example : NeutralPacket.B003.{v} = A003.{v} := by
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
example : NeutralPacket.B011.{v} = A011.{v} := by rfl
def A012 : Prop := ∀ (X : Type v) (f : ℕ → X → ℝ) (p : ℕ → X) (u : X) (N : ℕ),
  comparatorRegret f p u N = ∑ t ∈ Finset.range N, (f t (p t) - f t u)
example : NeutralPacket.B012.{v} = A012.{v} := by rfl
end DraftTypeVerification

namespace ActualTypeVerification
def propositionOf {P : Prop} (_ : P) : Prop := P
example : DraftTypeVerification.A001.{v} = propositionOf (@BanditRL.OnlineLearning.noRegret_limit_nonpos.{v}) := by rfl
example : DraftTypeVerification.A002.{v} = propositionOf (@BanditRL.OnlineLearning.limitNoRegret_implies_noRegret.{v}) := by rfl
example : DraftTypeVerification.A003.{v} = propositionOf (@BanditRL.OnlineLearning.limitNoRegret_iff_noRegret_of_converges.{v}) := by rfl
example : DraftTypeVerification.A004 = propositionOf (@BanditRL.OnlineLearning.NoRegretCounterexample.regret_eq) := by rfl
example : DraftTypeVerification.A005 = propositionOf (@BanditRL.OnlineLearning.NoRegretCounterexample.noRegret) := by rfl
example : DraftTypeVerification.A006 = propositionOf (@BanditRL.OnlineLearning.NoRegretCounterexample.normalized_even) := by rfl
example : DraftTypeVerification.A007 = propositionOf (@BanditRL.OnlineLearning.NoRegretCounterexample.normalized_odd) := by rfl
example : DraftTypeVerification.A008 = propositionOf (@BanditRL.OnlineLearning.NoRegretCounterexample.no_limit) := by rfl
example : DraftTypeVerification.A009 = propositionOf (@BanditRL.OnlineLearning.NoRegretCounterexample.strict_separation) := by rfl
example : DraftTypeVerification.A010 = propositionOf (@BanditRL.OnlineLearning.meanPredict_noRegret) := by rfl
example : DraftTypeVerification.A011.{v} = propositionOf (@BanditRL.OnlineLearning.noRegret_of_vanishing_bound.{v}) := by rfl
example : DraftTypeVerification.A012.{v} = propositionOf (@BanditRL.OnlineLearning.comparatorRegret_eq_sum.{v}) := by rfl
example : @NeutralPacket.r.{v} = @BanditRL.OnlineLearning.comparatorRegret.{v} := by rfl
example : @NeutralPacket.upper.{v} = @BanditRL.OnlineLearning.NoRegret.{v} := by rfl
example : @NeutralPacket.limit.{v} = @BanditRL.OnlineLearning.LimitNoRegret.{v} := by rfl
example : @NeutralPacket.h = @BanditRL.OnlineLearning.NoRegretCounterexample.potential := by rfl
example : @NeutralPacket.f = @BanditRL.OnlineLearning.NoRegretCounterexample.loss := by rfl
example : @NeutralPacket.q = @BanditRL.OnlineLearning.meanPredict := by rfl
open NoRegretSemanticsProbe

def C001 : Prop := ∀ (u : ℝ) (T : ℕ),
comparatorRegret linearLoss (fun _ => 0) u T = -(T : ℝ) * u
example : C001 = propositionOf (@NoRegretSemanticsProbe.linear_regret) := by rfl

def C002 : Prop := ∀ (u : ℝ) (T : ℕ) (hT : 0 < T),
comparatorRegret linearLoss (fun _ => 0) u T / T = -u
example : C002 = propositionOf (@NoRegretSemanticsProbe.linear_normalized) := by rfl

def C003 : Prop := ∀ (u : ℝ),
Tendsto (fun T : ℕ => comparatorRegret linearLoss (fun _ => 0) u T / T)
      atTop (nhds (-u))
example : C003 = propositionOf (@NoRegretSemanticsProbe.linear_converges) := by rfl

def C004 : Prop := LimitNoRegret (Set.Icc (0 : ℝ) 1) linearLoss (fun _ => 0)
example : C004 = propositionOf (@NoRegretSemanticsProbe.linear_literal) := by rfl

def C005 : Prop := NoRegret (Set.Icc (0 : ℝ) 1) linearLoss (fun _ => 0)
example : C005 = propositionOf (@NoRegretSemanticsProbe.linear_upper) := by rfl

def C006 : Prop := Tendsto (fun T : ℕ => comparatorRegret linearLoss (fun _ => 0) 1 T / T)
      atTop (nhds (-1)) ∧
    NoRegret (Set.Icc (0 : ℝ) 1) linearLoss (fun _ => 0) ∧ (-1 : ℝ) ≤ 0
example : C006 = propositionOf (@NoRegretSemanticsProbe.negative_limit_allowed) := by rfl

def C007 : Prop := LimitNoRegret (Set.Icc (0 : ℝ) 1) linearLoss (fun _ => 0) ↔
      NoRegret (Set.Icc (0 : ℝ) 1) linearLoss (fun _ => 0)
example : C007 = propositionOf (@NoRegretSemanticsProbe.iff_on_linear) := by rfl

def C008 : Prop := NoRegret (Set.Icc (0 : ℝ) 1) (fun (_ : ℕ) x => x ^ 2)
      (meanPredict (fun _ => 0))
example : C008 = propositionOf (@NoRegretSemanticsProbe.actual_mean_upper) := by rfl

def C009 : Prop := comparatorRegret (fun (_ : ℕ) x => x ^ 2) (meanPredict (fun _ => 0)) 1 2 / 2 =
      (-7 : ℝ) / 8
example : C009 = propositionOf (@NoRegretSemanticsProbe.actual_mean_negative_T2) := by rfl

def C010 : Prop := (0 : ℝ) ∈ Set.Icc 0 1 ∧ (1 : ℝ) ∈ Set.Icc 0 1 ∧
      ∀ t : ℕ, (fun (_ : ℕ) => (0 : ℝ)) t ∈ Set.Icc 0 1
example : C010 = propositionOf (@NoRegretSemanticsProbe.obstruction_feasible) := by rfl

def C011 : Prop := NoRegretCounterexample.loss 0 1 = 0 ∧
    NoRegretCounterexample.loss 1 1 = 2 ∧
    NoRegretCounterexample.loss 2 1 = -2 ∧
    NoRegretCounterexample.loss 3 1 = 4
example : C011 = propositionOf (@NoRegretSemanticsProbe.actual_signed_losses) := by rfl

def C012 : Prop := comparatorRegret NoRegretCounterexample.loss (fun _ => 0) 1 0 = 0
example : C012 = propositionOf (@NoRegretSemanticsProbe.zero_horizon) := by rfl

def C013 : Prop := comparatorRegret NoRegretCounterexample.loss (fun _ => 0) 1 2 / 2 = -1
example : C013 = propositionOf (@NoRegretSemanticsProbe.even_T2) := by rfl

def C014 : Prop := comparatorRegret NoRegretCounterexample.loss (fun _ => 0) 1 3 / 3 = 0
example : C014 = propositionOf (@NoRegretSemanticsProbe.odd_T3) := by rfl

def C015 : Prop := NoRegret (Set.Icc (0 : ℝ) 1) NoRegretCounterexample.loss (fun _ => 0) ∧
      ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) NoRegretCounterexample.loss (fun _ => 0)
example : C015 = propositionOf (@NoRegretSemanticsProbe.same_process_strict) := by rfl

noncomputable def linearFixture (_ : ℕ) (u : ℝ) : ℝ := u
example : linearFixture = NoRegretSemanticsProbe.linearLoss := by rfl
end ActualTypeVerification
