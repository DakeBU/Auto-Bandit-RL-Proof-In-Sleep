import BanditRLProof.OnlineLearningMean
import BanditRLProof.OnlineLearningRegret
import BanditRLProof.Exp3ConditionalMoments
import Mathlib.Data.List.Count
import Mathlib.Data.Fintype.Vector
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory Finset Set
namespace BanditRL.OnlineLearning.GuessingLower

/-- History is newest-first: adding b records the next revealed bit after the prediction. -/
noncomputable def polyaNext (h : List Bool) : ℝ :=
  ((h.count true : ℝ) + 1) / ((h.length : ℝ) + 2)

/-- Actual recursively generated path mass; it does not depend on a learner or seed. -/
noncomputable def pathWeight (h : List Bool) : ℝ :=
  match h with
  | [] => 1
  | b :: past => pathWeight past * (if b then polyaNext past else 1 - polyaNext past)

/-- Convert newest-first finite history into chronological labels, padded by false after its end. -/
def binaryStream (h : List Bool) (t : ℕ) : Bool :=
  (h.reverse[t]?).getD false

def binaryValues (h : List Bool) (t : ℕ) : ℝ :=
  if binaryStream h t then 1 else 0

/-- One policy of strict-past labels; no current label or future sequence is passed to A. -/
noncomputable def causalPredict (A : List Bool → ℝ) (y : ℕ → Bool) (t : ℕ) : ℝ :=
  A (List.ofFn (fun i : Fin t => y i)).reverse

/-- Actual shared comparator regret against the feasible empirical-mean hindsight minimizer. -/
noncomputable def pathRegret (A : List Bool → ℝ) (h : List Bool) : ℝ :=
  comparatorRegret (fun t x => (x - binaryValues h t)^2)
    (causalPredict A (binaryStream h)) (empiricalMean (binaryValues h) h.length) h.length

noncomputable def pathExpectation (T : ℕ) (f : List Bool → ℝ) : ℝ :=
  ∑ v : List.Vector Bool T, pathWeight v.toList * f v.toList

/-- Same finite-action Dirac law as the shared Bandit library, instantiated at binary histories. -/
noncomputable def prefixMeasure (T : ℕ) [MeasurableSpace (List.Vector Bool T)] :
    Measure (List.Vector Bool T) :=
  BanditRLProof.Exp3.finiteActionMeasure univ (fun v => pathWeight v.toList)

def shape_probability_mem (h : List Bool) : Prop :=
  polyaNext h ∈ Ioo (0 : ℝ) 1

def shape_branch_mass (h : List Bool) : Prop :=
  pathWeight (false :: h) + pathWeight (true :: h) = pathWeight h

def shape_pathWeight_nonneg (h : List Bool) : Prop :=
  0 ≤ pathWeight h

def shape_prefix_mass_one (T : ℕ) : Prop :=
  (∑ v : List.Vector Bool T, pathWeight v.toList) = 1

def shape_prefix_distribution (T : ℕ) : Prop :=
  BanditRLProof.Exp3.FiniteActionDistribution (univ : Finset (List.Vector Bool T)) (fun v => pathWeight v.toList)

def shape_prefixMeasure_probability (T : ℕ) [MeasurableSpace (List.Vector Bool T)] [MeasurableSingletonClass (List.Vector Bool T)] : Prop :=
  IsProbabilityMeasure (prefixMeasure T)

def shape_pathExpectation_integral (T : ℕ) [MeasurableSpace (List.Vector Bool T)] [MeasurableSingletonClass (List.Vector Bool T)] (f : List Bool → ℝ) : Prop :=
  (∫ v, f v.toList ∂prefixMeasure T) = pathExpectation T f

def shape_expected_heads (T : ℕ) : Prop :=
  pathExpectation T (fun h => (h.count true : ℝ)) = (T : ℝ) / 2

def shape_expected_heads_sq (T : ℕ) : Prop :=
  pathExpectation T (fun h => (h.count true : ℝ)^2) = (T : ℝ) * (2 * (T : ℝ) + 1) / 6

def shape_expected_next_variance (T : ℕ) : Prop :=
  pathExpectation T (fun h => polyaNext h * (1 - polyaNext h)) = ((T : ℝ) + 3) / (6 * ((T : ℝ) + 2))

def shape_causalPredict_prefix (A : List Bool → ℝ) (y z : ℕ → Bool) (t : ℕ) (hpast : ∀ i < t, y i = z i) : Prop :=
  causalPredict A y t = causalPredict A z t

def shape_binary_mean_minimizer (h : List Bool) (hpos : 0 < h.length) : Prop :=
  empiricalMean (binaryValues h) h.length ∈ Icc (0 : ℝ) 1 ∧ ∀ u ∈ Icc (0 : ℝ) 1, (∑ t ∈ range h.length, (empiricalMean (binaryValues h) h.length - binaryValues h t)^2) ≤ ∑ t ∈ range h.length, (u - binaryValues h t)^2

def shape_conditional_square_lower (h : List Bool) (x : ℝ) : Prop :=
  polyaNext h * (1 - polyaNext h) ≤ (1 - polyaNext h) * x^2 + polyaNext h * (x - 1)^2

def shape_expected_pathRegret_lower (A : List Bool → ℝ) (T : ℕ) (hT : 0 < T) : Prop :=
  (harmonic (T + 1) : ℝ) / 6 ≤ pathExpectation T (pathRegret A)

def shape_randomized_harmonic_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (hbound : ∀ ω h, A ω h ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T) : Prop :=
  ∃ v : List.Vector Bool T, (harmonic (T + 1) : ℝ) / 6 ≤ ∫ ω, pathRegret (A ω) v.toList ∂μ

def shape_randomized_log_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (hbound : ∀ ω h, A ω h ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T) : Prop :=
  ∃ v : List.Vector Bool T, Real.log ((T : ℝ) + 2) / 6 ≤ ∫ ω, pathRegret (A ω) v.toList ∂μ

end BanditRL.OnlineLearning.GuessingLower
