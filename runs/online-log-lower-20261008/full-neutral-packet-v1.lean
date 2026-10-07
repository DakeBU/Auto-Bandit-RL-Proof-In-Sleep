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

noncomputable def f9 (A : List Bool → ℝ) (h : List Bool) : ℝ :=
  ∑ t ∈ range h.length, (f5 A (f3 h) t - f4 h t)^2
noncomputable def f10 (h : List Bool) : ℝ :=
  ∑ t ∈ range h.length, (m (f4 h) h.length - f4 h t)^2
noncomputable def f11 : Measure Bool := law univ (fun _ => (1 : ℝ)/2)
def f12 (b : Bool) (_h : List Bool) : ℝ := if b then 1 else 0

universe u
def B001 : Prop :=
  ∀ (h, List Bool) : f1 h ∈ Ioo (0 : ℝ) 1

def B002 : Prop :=
  ∀ (h, List Bool) : f2 (false :: h) + f2 (true :: h) = f2 h

def B003 : Prop :=
  ∀ (h, List Bool) : 0 ≤ f2 h

def B004 : Prop :=
  ∀ (T, ℕ) (f : List Bool → ℝ) : (∑ v : List.Vector Bool (T + 1), f v.toList) = ∑ v : List.Vector Bool T, (f (false :: v.toList) + f (true :: v.toList))

def B005 : Prop :=
  ∀ (T, ℕ) : (∑ v : List.Vector Bool T, f2 v.toList) = 1

def B006 : Prop :=
  ∀ (T, ℕ) : P (univ : Finset (List.Vector Bool T)) (fun v => f2 v.toList)

def B007 : Prop :=
  ∀ (T, ℕ) [MeasurableSpace (List.Vector Bool T)] [MeasurableSingletonClass (List.Vector Bool T)] : IsProbabilityMeasure (f8 T)

def B008 : Prop :=
  ∀ (T, ℕ) [MeasurableSpace (List.Vector Bool T)] [MeasurableSingletonClass (List.Vector Bool T)] (f : List Bool → ℝ) : (∫ v, f v.toList ∂f8 T) = f7 T f

def B009 : Prop :=
  ∀ (T, ℕ) (f g : List Bool → ℝ) (hfg : ∀ h, h.length = T → f h = g h) : f7 T f = f7 T g

def B010 : Prop :=
  ∀ (T, ℕ) (c : ℝ) : f7 T (fun _ => c) = c

def B011 : Prop :=
  ∀ (T, ℕ) (f g : List Bool → ℝ) : f7 T (fun h => f h + g h) = f7 T f + f7 T g

def B012 : Prop :=
  ∀ (T, ℕ) (f g : List Bool → ℝ) : f7 T (fun h => f h - g h) = f7 T f - f7 T g

def B013 : Prop :=
  ∀ (T, ℕ) (c : ℝ) (f : List Bool → ℝ) : f7 T (fun h => c * f h) = c * f7 T f

def B014 : Prop :=
  ∀ (T, ℕ) (f : List Bool → ℝ) (c : ℝ) : f7 T (fun h => f h / c) = f7 T f / c

def B015 : Prop :=
  ∀ (T, ℕ) (f : List Bool → ℝ) : f7 (T + 1) f = f7 T (fun h => (1 - f1 h) * f (false :: h) + f1 h * f (true :: h))

def B016 : Prop :=
  ∀ (T, ℕ) : f7 (T + 1) (fun h => (h.count true : ℝ)) = f7 T (fun h => (h.count true : ℝ)) + (f7 T (fun h => (h.count true : ℝ)) + 1) / ((T : ℝ) + 2)

def B017 : Prop :=
  ∀ (T, ℕ) : f7 (T + 1) (fun h => (h.count true : ℝ)^2) = f7 T (fun h => (h.count true : ℝ)^2) + (2 * f7 T (fun h => (h.count true : ℝ)^2) + 3 * f7 T (fun h => (h.count true : ℝ)) + 1) / ((T : ℝ) + 2)

def B018 : Prop :=
  ∀ (T, ℕ) : f7 T (fun h => (h.count true : ℝ)) = (T : ℝ) / 2

def B019 : Prop :=
  ∀ (T, ℕ) : f7 T (fun h => (h.count true : ℝ)^2) = (T : ℝ) * (2 * (T : ℝ) + 1) / 6

def B020 : Prop :=
  ∀ (T, ℕ) : f7 T (fun h => f1 h * (1 - f1 h)) = ((T : ℝ) + 3) / (6 * ((T : ℝ) + 2))

def B021 : Prop :=
  ∀ (A, List Bool → ℝ) (y z : ℕ → Bool) (t : ℕ) (hpast : ∀ i < t, y i = z i) : f5 A y t = f5 A z t

def B022 : Prop :=
  ∀ (h, List Bool) (hpos : 0 < h.length) : m (f4 h) h.length ∈ Icc (0 : ℝ) 1 ∧ ∀ u ∈ Icc (0 : ℝ) 1, (∑ t ∈ range h.length, (m (f4 h) h.length - f4 h t)^2) ≤ ∑ t ∈ range h.length, (u - f4 h t)^2

def B023 : Prop :=
  ∀ (h, List Bool) (x : ℝ) : f1 h * (1 - f1 h) ≤ (1 - f1 h) * x^2 + f1 h * (x - 1)^2

def B024 : Prop :=
  ∀ (b, Bool) (h : List Bool) (t : ℕ) (ht : t < h.length) : f3 (b :: h) t = f3 h t

def B025 : Prop :=
  ∀ (b, Bool) (h : List Bool) : f3 (b :: h) h.length = b

def B026 : Prop :=
  ∀ (b, Bool) (h : List Bool) (t : ℕ) (ht : t < h.length) : f4 (b :: h) t = f4 h t

def B027 : Prop :=
  ∀ (A, List Bool → ℝ) (h : List Bool) : f5 A (f3 h) h.length = A h

def B028 : Prop :=
  ∀ (A, List Bool → ℝ) (b : Bool) (h : List Bool) : f5 A (f3 (b :: h)) h.length = A h

def B029 : Prop :=
  ∀ (A, List Bool → ℝ) (h : List Bool) : f6 A h = f9 A h - f10 h

def B030 : Prop :=
  ∀ (A, List Bool → ℝ) (b : Bool) (h : List Bool) : f9 A (b :: h) = f9 A h + (A h - if b then 1 else 0)^2

def B031 : Prop :=
  ∀ (h, List Bool) : (∑ t ∈ range h.length, f4 h t) = (h.count true : ℝ)

def B032 : Prop :=
  ∀ (h, List Bool) (t : ℕ) : (f4 h t)^2 = f4 h t

def B033 : Prop :=
  ∀ (h, List Bool) (hpos : 0 < h.length) : f10 h = (h.count true : ℝ) - (h.count true : ℝ)^2 / (h.length : ℝ)

def B034 : Prop :=
  ∀ (T, ℕ) (hT : 0 < T) : f7 T f10 = ((T : ℝ) - 1) / 6

def B035 : Prop :=
  ∀ (T, ℕ) (f g : List Bool → ℝ) (hfg : ∀ h, h.length = T → f h ≤ g h) : f7 T f ≤ f7 T g

def B036 : Prop :=
  ∀ (A, List Bool → ℝ) (T : ℕ) : f7 (T + 1) (f9 A) = f7 T (f9 A) + f7 T (fun h => (1 - f1 h) * (A h)^2 + f1 h * (A h - 1)^2)

def B037 : Prop :=
  ∀ (A, List Bool → ℝ) (T : ℕ) : f7 T (f9 A) + ((T : ℝ) + 3) / (6 * ((T : ℝ) + 2)) ≤ f7 (T + 1) (f9 A)

def B038 : Prop :=
  ∀ (T, ℕ) : (∑ t ∈ range T, ((t : ℝ) + 3) / (6 * ((t : ℝ) + 2))) = (T : ℝ) / 6 + ((harmonic (T + 1) : ℝ) - 1) / 6

def B039 : Prop :=
  ∀ (A, List Bool → ℝ) (T : ℕ) : (∑ t ∈ range T, ((t : ℝ) + 3) / (6 * ((t : ℝ) + 2))) ≤ f7 T (f9 A)

def B040 : Prop :=
  ∀ (A, List Bool → ℝ) (T : ℕ) (hT : 0 < T) : (harmonic (T + 1) : ℝ) / 6 ≤ f7 T (f6 A)

def B041 : Prop :=
  ∀ (h, List Bool) : 0 < f2 h

def B042 : Prop :=
  ∀ (x y, ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) : (x - y)^2 ∈ Icc (0 : ℝ) 1

def B043 : Prop :=
  ∀ (T, ℕ) (p y : ℕ → ℝ) (hp : ∀ t < T, p t ∈ Icc (0 : ℝ) 1) (hy : ∀ t < T, y t ∈ Icc (0 : ℝ) 1) : (∑ t ∈ range T, (p t - y t)^2) ∈ Icc (0 : ℝ) T

def B044 : Prop :=
  ∀ (A, List Bool → ℝ) (h : List Bool) (hbound : ∀ k, A k ∈ Icc (0 : ℝ) 1) : |f6 A h| ≤ (h.length : ℝ)

def B045 : Prop :=
  ∀ {Ω, Type*} [MeasurableSpace Ω] (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (h : List Bool) : Measurable (fun ω => f6 (A ω) h)

def B046 : Prop :=
  ∀ {Ω, Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (hbound : ∀ ω h, A ω h ∈ Icc (0 : ℝ) 1) (h : List Bool) : Integrable (fun ω => f6 (A ω) h) μ

def B047 : Prop :=
  ∀ {Ω, Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (hbound : ∀ ω h, A ω h ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T) : ∃ v : List.Vector Bool T, (harmonic (T + 1) : ℝ) / 6 ≤ ∫ ω, f6 (A ω) v.toList ∂μ

def B048 : Prop :=
  ∀ {Ω, Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (hbound : ∀ ω h, A ω h ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T) : ∃ v : List.Vector Bool T, Real.log ((T : ℝ) + 2) / 6 ≤ ∫ ω, f6 (A ω) v.toList ∂μ

def B049 : Prop :=
  f1 [true,true,true] = (4 : ℝ)/5 ∧ f1 [true,true,true] ∈ Ioo (0 : ℝ) 1

def B050 : Prop :=
  f2 [true,true] = (1 : ℝ)/3 ∧ f2 [false,false] = (1 : ℝ)/3 ∧ f2 [true,false] = (1 : ℝ)/6 ∧ f2 [false,true] = (1 : ℝ)/6

def B051 : Prop :=
  (∑ v : List.Vector Bool 0, f2 v.toList) = 1 ∧ (∑ v : List.Vector Bool 2, f2 v.toList) = 1

def B052 : Prop :=
  f7 2 (fun h => (h.count true : ℝ)) = 1 ∧ f7 2 (fun h => (h.count true : ℝ)^2) = (5 : ℝ)/3

def B053 : Prop :=
  f7 2 (fun h => f1 h * (1-f1 h)) = (5 : ℝ)/24

def B054 : Prop :=
  f5 f1 (f3 [true,false]) 1 = f5 f1 (f3 [false,false]) 1

def B055 : Prop :=
  f5 f1 (f3 [true,true,false]) 2 = (1 : ℝ)/2

def B056 : Prop :=
  f6 f1 [true,true] = (13 : ℝ)/36

def B057 : Prop :=
  f10 [true,false] = (1 : ℝ)/2

def B058 : Prop :=
  (1 : ℝ)/4 ≤ f7 1 (f6 f1)

def B059 : Prop :=
  P (univ : Finset Bool) (fun _ => (1 : ℝ)/2)

def B060 : Prop :=
  ∀ b h, f12 b h ∈ Icc (0 : ℝ) 1

def B061 : Prop :=
  f12 true [] = 1 ∧ f12 false [] = 0 ∧ f11 {true} = (1 : ENNReal)/2 ∧ f11 {false} = (1 : ENNReal)/2

def B062 : Prop :=
  ∃ v : List.Vector Bool 2, (11 : ℝ)/36 ≤ ∫ b, f6 (f12 b) v.toList ∂f11

def B063 : Prop :=
  ∃ v : List.Vector Bool 2, Real.log 4 / 6 ≤ ∫ b, f6 (f12 b) v.toList ∂f11

def B064 : Prop :=
  ∀ (T, ℕ) (hT : 0 < T) : ∃ v : List.Vector Bool T, Real.log ((T : ℝ)+2)/6 ≤ f6 f1 v.toList

end NeutralContext
