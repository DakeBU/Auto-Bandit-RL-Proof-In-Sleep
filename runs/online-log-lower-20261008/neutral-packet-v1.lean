import Mathlib.Data.List.Count
import Mathlib.Data.Fintype.Vector
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
noncomputable section
open MeasureTheory Finset Set
namespace NeutralContext
noncomputable def r {X : Type*} (loss : ℕ → X → ℝ) (p : ℕ → X) (u : X) (T : ℕ) : ℝ :=
  (∑ t ∈ range T, loss t (p t)) - ∑ t ∈ range T, loss t u
noncomputable def m (y : ℕ → ℝ) (n : ℕ) : ℝ := (∑ t ∈ range n, y t) / n
structure P {X : Type*} (arms : Finset X) (p : X → ℝ) : Prop where
  nonneg : ∀ x ∈ arms, 0 ≤ p x
  sum_eq_one : arms.sum p = 1
noncomputable def law {X : Type*} [MeasurableSpace X] (arms : Finset X) (p : X → ℝ) : Measure X :=
  arms.sum (fun x => ENNReal.ofReal (p x) • Measure.dirac x)

noncomputable def f1 (h : List Bool) : ℝ :=
  ((h.count true : ℝ) + 1) / ((h.length : ℝ) + 2)

noncomputable def f2 (h : List Bool) : ℝ :=
  match h with
  | [] => 1
  | b :: past => f2 past * (if b then f1 past else 1 - f1 past)

def f3 (h : List Bool) (t : ℕ) : Bool :=
  (h.reverse[t]?).getD false

def f4 (h : List Bool) (t : ℕ) : ℝ :=
  if f3 h t then 1 else 0

noncomputable def f5 (A : List Bool → ℝ) (y : ℕ → Bool) (t : ℕ) : ℝ :=
  A (List.ofFn (fun i : Fin t => y i)).reverse

noncomputable def f6 (A : List Bool → ℝ) (h : List Bool) : ℝ :=
  r (fun t x => (x - f4 h t)^2)
    (f5 A (f3 h)) (m (f4 h) h.length) h.length

noncomputable def f7 (T : ℕ) (f : List Bool → ℝ) : ℝ :=
  ∑ v : List.Vector Bool T, f2 v.toList * f v.toList

noncomputable def f8 (T : ℕ) [MeasurableSpace (List.Vector Bool T)] :
    Measure (List.Vector Bool T) :=
  law univ (fun v => f2 v.toList)

def N01 (h : List Bool) : Prop :=
  f1 h ∈ Ioo (0 : ℝ) 1

def N02 (h : List Bool) : Prop :=
  f2 (false :: h) + f2 (true :: h) = f2 h

def N03 (h : List Bool) : Prop :=
  0 ≤ f2 h

def N04 (T : ℕ) : Prop :=
  (∑ v : List.Vector Bool T, f2 v.toList) = 1

def N05 (T : ℕ) : Prop :=
  P (univ : Finset (List.Vector Bool T)) (fun v => f2 v.toList)

def N06 (T : ℕ) [MeasurableSpace (List.Vector Bool T)] [MeasurableSingletonClass (List.Vector Bool T)] : Prop :=
  IsProbabilityMeasure (f8 T)

def N07 (T : ℕ) [MeasurableSpace (List.Vector Bool T)] [MeasurableSingletonClass (List.Vector Bool T)] (f : List Bool → ℝ) : Prop :=
  (∫ v, f v.toList ∂f8 T) = f7 T f

def N08 (T : ℕ) : Prop :=
  f7 T (fun h => (h.count true : ℝ)) = (T : ℝ) / 2

def N09 (T : ℕ) : Prop :=
  f7 T (fun h => (h.count true : ℝ)^2) = (T : ℝ) * (2 * (T : ℝ) + 1) / 6

def N10 (T : ℕ) : Prop :=
  f7 T (fun h => f1 h * (1 - f1 h)) = ((T : ℝ) + 3) / (6 * ((T : ℝ) + 2))

def N11 (A : List Bool → ℝ) (y z : ℕ → Bool) (t : ℕ) (hpast : ∀ i < t, y i = z i) : Prop :=
  f5 A y t = f5 A z t

def N12 (h : List Bool) (hpos : 0 < h.length) : Prop :=
  m (f4 h) h.length ∈ Icc (0 : ℝ) 1 ∧ ∀ u ∈ Icc (0 : ℝ) 1, (∑ t ∈ range h.length, (m (f4 h) h.length - f4 h t)^2) ≤ ∑ t ∈ range h.length, (u - f4 h t)^2

def N13 (h : List Bool) (x : ℝ) : Prop :=
  f1 h * (1 - f1 h) ≤ (1 - f1 h) * x^2 + f1 h * (x - 1)^2

def N14 (A : List Bool → ℝ) (T : ℕ) (hT : 0 < T) : Prop :=
  (harmonic (T + 1) : ℝ) / 6 ≤ f7 T (f6 A)

def N15 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (hbound : ∀ ω h, A ω h ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T) : Prop :=
  ∃ v : List.Vector Bool T, (harmonic (T + 1) : ℝ) / 6 ≤ ∫ ω, f6 (A ω) v.toList ∂μ

def N16 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (hbound : ∀ ω h, A ω h ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T) : Prop :=
  ∃ v : List.Vector Bool T, Real.log ((T : ℝ) + 2) / 6 ≤ ∫ ω, f6 (A ω) v.toList ∂μ

end NeutralContext
