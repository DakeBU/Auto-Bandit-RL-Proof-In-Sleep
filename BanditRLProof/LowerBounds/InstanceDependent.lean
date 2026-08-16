import BanditRLProof.LowerBounds.Minimax
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Instance-dependent lower-bound dependencies

This file starts the source-faithful Chapter 16 spine for Lattimore--Szepesvári,
*Bandit Algorithms* (2020).  The compiled surface freezes the exact
subpolynomial consistency quantifier, the distribution-class `d_inf`
definition, a parameterized candidate interface, and Gaussian alternative
costs.  It also isolates the elementary asymptotic step saying that two
consistent regret sequences are eventually dominated by every positive power.

It deliberately does **not** claim Theorem 16.2, Lemma 16.3, or Theorem 16.4.
Those terminals depend on Chapter 15's still-blocked same-policy adaptive
history divergence decomposition and on a canonical stochastic-policy history
law.
-/

namespace BanditRLProof
namespace LowerBounds

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

/-- The exact scalar asymptotic quantifier in Definition 16.1: a nonnegative
regret sequence is smaller than every positive polynomial order.  Regret
nonnegativity is kept outside this analytic predicate so callers must expose
the model-specific fact explicitly. -/
def IsConsistentRegret (regret : Nat -> Real) : Prop :=
  forall p : Real, 0 < p ->
    Tendsto (fun n : Nat => regret n / (n : Real) ^ p) atTop (nhds 0)

/-- Definition 16.1 over an abstract policy/environment regret interface.
This preserves the source quantifier order: one policy, every environment in
the class, and every positive real exponent. -/
def IsConsistentPolicyOver
    {Policy Environment : Type*}
    (environmentClass : Set Environment)
    (regret : Policy -> Environment -> Nat -> Real)
    (policy : Policy) : Prop :=
  forall environment, environment ∈ environmentClass ->
    IsConsistentRegret (regret policy environment)

/-- The sum of two source-consistent regret sequences is still consistent.
This is the closure step used for `R_n(nu) + R_n(nu')` in the proof of
Theorem 16.2. -/
theorem IsConsistentRegret.add
    {first second : Nat -> Real}
    (hfirst : IsConsistentRegret first)
    (hsecond : IsConsistentRegret second) :
    IsConsistentRegret (fun n => first n + second n) := by
  intro p hp
  simpa only [add_div, zero_add] using (hfirst p hp).add (hsecond p hp)

/-- Two consistent regret sequences are eventually at most `n^p` for every
positive exponent `p`.  This is a stronger eventual form of the source's
auxiliary `C_p n^p` bound and avoids introducing an opaque constant. -/
theorem IsConsistentRegret.eventually_add_le_rpow
    {first second : Nat -> Real}
    (hfirst : IsConsistentRegret first)
    (hsecond : IsConsistentRegret second)
    {p : Real} (hp : 0 < p) :
    ∀ᶠ n : Nat in atTop,
      first n + second n <= (n : Real) ^ p := by
  have hlimit := hfirst.add hsecond p hp
  have hratio : ∀ᶠ n : Nat in atTop,
      (first n + second n) / (n : Real) ^ p < 1 :=
    hlimit.eventually_lt_const zero_lt_one
  filter_upwards [hratio, eventually_gt_atTop (0 : Nat)] with n hn hnpos
  have hcast : (0 : Real) < n := by exact_mod_cast hnpos
  have hpow : (0 : Real) < (n : Real) ^ p := Real.rpow_pos_of_pos hcast p
  have := (div_le_iff₀ hpow).mp hn.le
  simpa using this

/-- Eventually, the logarithmic growth ratio of a positive sum of two
consistent regrets is at most every positive exponent.  This is the
direction-correct analytic leaf used before the source takes a limsup. -/
theorem IsConsistentRegret.eventually_log_add_div_log_le
    {first second : Nat -> Real}
    (hfirst : IsConsistentRegret first)
    (hsecond : IsConsistentRegret second)
    (hpositive : ∀ᶠ n : Nat in atTop, 0 < first n + second n)
    {p : Real} (hp : 0 < p) :
    ∀ᶠ n : Nat in atTop,
      Real.log (first n + second n) / Real.log n <= p := by
  filter_upwards [hfirst.eventually_add_le_rpow hsecond hp, hpositive,
      eventually_gt_atTop (1 : Nat)] with n hupper hsum hn
  have hnreal : (1 : Real) < n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log (n : Real) := Real.log_pos hnreal
  have hlogle : Real.log (first n + second n) <=
      Real.log ((n : Real) ^ p) :=
    Real.log_le_log hsum hupper
  rw [Real.log_rpow (zero_lt_one.trans hnreal) p] at hlogle
  exact (div_le_iff₀ hlogpos).2 hlogle

/-- The source quantity
`d_inf(P, muStar, M) = inf {D(P,P') : P' in M, mean(P') > muStar}`.
The value is extended-real, so an empty alternative set has infimum `∞` and
support failures remain visible. -/
def divergenceInfimum
    {Reward : Type*} [MeasurableSpace Reward]
    (P : Measure Reward) (muStar : Real)
    (distributionClass : Set (Measure Reward))
    (mean : Measure Reward -> Real) : ENNReal :=
  sInf {cost : ENNReal |
    exists P' : Measure Reward,
      P' ∈ distributionClass /\ muStar < mean P' /\
        cost = relativeEntropy P P'}

/-- Any admissible confusing alternative upper-bounds `d_inf`, with KL in the
source direction from the original law to the alternative law. -/
theorem divergenceInfimum_le
    {Reward : Type*} [MeasurableSpace Reward]
    {P P' : Measure Reward} {muStar : Real}
    {distributionClass : Set (Measure Reward)}
    {mean : Measure Reward -> Real}
    (hclass : P' ∈ distributionClass)
    (hbetter : muStar < mean P') :
    divergenceInfimum P muStar distributionClass mean <=
      relativeEntropy P P' := by
  apply sInf_le
  exact ⟨P', hclass, hbetter, rfl⟩

/-- Parameterized form of `d_inf`, useful when a distribution class is
presented by a family of laws rather than an injective set-level mean map. -/
def parametricDivergenceInfimum
    {Reward Parameter : Type*} [MeasurableSpace Reward]
    (law : Parameter -> Measure Reward) (mean : Parameter -> Real)
    (parameter : Parameter) (muStar : Real) : ENNReal :=
  sInf {cost : ENNReal |
    exists alternative : Parameter,
      muStar < mean alternative /\
        cost = relativeEntropy (law parameter) (law alternative)}

/-- Candidate inequality for the parameterized `d_inf` surface. -/
theorem parametricDivergenceInfimum_le
    {Reward Parameter : Type*} [MeasurableSpace Reward]
    {law : Parameter -> Measure Reward} {mean : Parameter -> Real}
    {parameter alternative : Parameter} {muStar : Real}
    (hbetter : muStar < mean alternative) :
    parametricDivergenceInfimum law mean parameter muStar <=
      relativeEntropy (law parameter) (law alternative) := by
  apply sInf_le
  exact ⟨alternative, hbetter, rfl⟩

/-- Unit-variance Gaussian specialization of the source `d_inf`. -/
abbrev unitGaussianDivergenceInfimum (mu muStar : Real) : ENNReal :=
  parametricDivergenceInfimum unitGaussianArm id mu muStar

/-- A Gaussian alternative with mean `muStar + epsilon` is admissible and has
the exact arm-level information cost shown here.  Taking `epsilon -> 0` is a
separate infimum/limit leaf and is not hidden in this theorem. -/
theorem unitGaussianDivergenceInfimum_le_perturbed
    (mu muStar epsilon : Real) (hepsilon : 0 < epsilon) :
    unitGaussianDivergenceInfimum mu muStar <=
      ENNReal.ofReal (((muStar - mu) + epsilon) ^ 2 / 2) := by
  calc
    unitGaussianDivergenceInfimum mu muStar <=
        relativeEntropy (unitGaussianArm mu)
          (unitGaussianArm (muStar + epsilon)) := by
      apply parametricDivergenceInfimum_le
      simpa using lt_add_of_pos_right muStar hepsilon
    _ = ENNReal.ofReal ((mu - (muStar + epsilon)) ^ 2 / 2) :=
      klDiv_gaussianReal_one mu (muStar + epsilon)
    _ = ENNReal.ofReal (((muStar - mu) + epsilon) ^ 2 / 2) := by
      congr 1
      ring

end

end LowerBounds
end BanditRLProof
