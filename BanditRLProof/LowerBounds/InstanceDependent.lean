import BanditRLProof.LowerBounds.Minimax
import BanditRLProof.LowerBounds.BanditHistoryKL
import BanditRLProof.LowerBounds.GaussianMinimax
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Instance-dependent lower-bound dependencies

This file starts the source-faithful Chapter 16 spine for Lattimore--Szepesvári,
*Bandit Algorithms* (2020).  The compiled surface freezes the exact
subpolynomial consistency quantifier, the distribution-class `d_inf`
definition, the exact unit-Gaussian row of Table 16.1, the one-arm
change-of-measure/event-information layer built on the compiled Chapter 15
history-KL identity, and the canonical gap-times-pull-count event-to-regret
producers.  It also isolates the elementary asymptotic and scalar logarithmic
steps used by the source proof.

The source finite-mean environment bridge, exact Lemma 16.3, exact
unit-variance Gaussian Theorem 16.4, and Theorem 16.2 compile. The latter
uses extended-real inverse-infimum aggregation and finite-count Fatou,
retaining zero, finite, infinite, and empty-alternative information branches.
-/

namespace BanditRLProof
namespace LowerBounds

open Filter MeasureTheory ProbabilityTheory Set
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

/-- A finite-armed product environment whose arm laws have certified finite
means.  The `mean` field is intentionally tied to the Bochner integral rather
than treated as an unrelated parameter: this is the source-level bridge used
when an unchanged arm law must imply an unchanged arm mean. -/
structure FiniteMeanBanditEnvironment (K : Nat) where
  armLaw : Kernel (Fin K) Real
  armLaw_isMarkov : IsMarkovKernel armLaw
  mean : Fin K -> Real
  integrable_id : forall arm, Integrable id (armLaw arm)
  mean_eq_integral : forall arm, mean arm = ∫ reward, reward ∂armLaw arm
  bestArm : Fin K
  isBest : forall arm, mean arm <= mean bestArm

instance finiteMeanBanditEnvironmentIsMarkovKernel
    {K : Nat} (environment : FiniteMeanBanditEnvironment K) :
    IsMarkovKernel environment.armLaw :=
  environment.armLaw_isMarkov

/-- The source gap `Delta_i(nu) = muStar(nu) - mu_i(nu)`. -/
def FiniteMeanBanditEnvironment.gap
    {K : Nat} (environment : FiniteMeanBanditEnvironment K)
    (arm : Fin K) : Real :=
  environment.mean environment.bestArm - environment.mean arm

theorem FiniteMeanBanditEnvironment.gap_nonneg
    {K : Nat} (environment : FiniteMeanBanditEnvironment K)
    (arm : Fin K) :
    0 <= environment.gap arm := by
  exact sub_nonneg.mpr (environment.isBest arm)

@[simp]
theorem FiniteMeanBanditEnvironment.gap_bestArm
    {K : Nat} (environment : FiniteMeanBanditEnvironment K) :
    environment.gap environment.bestArm = 0 := by
  simp [FiniteMeanBanditEnvironment.gap]

/-- The mean increase `lambda` of the single changed arm in Lemma 16.3. -/
def oneArmMeanIncrease
    {K : Nat} (original reference : FiniteMeanBanditEnvironment K)
    (changedArm : Fin K) : Real :=
  reference.mean changedArm - original.mean changedArm

/-- The changed environment's advantage over the original optimal mean,
`lambda - Delta_i(nu)`, in the exact second branch of Lemma 16.3's minimum. -/
def oneArmChangedMargin
    {K : Nat} (original reference : FiniteMeanBanditEnvironment K)
    (changedArm : Fin K) : Real :=
  reference.mean changedArm - original.mean original.bestArm

/-- Equal arm laws have equal certified finite means. -/
theorem FiniteMeanBanditEnvironment.mean_eq_of_armLaw_eq
    {K : Nat} (first second : FiniteMeanBanditEnvironment K)
    (arm : Fin K) (hlaw : first.armLaw arm = second.armLaw arm) :
    first.mean arm = second.mean arm := by
  rw [first.mean_eq_integral arm, second.mean_eq_integral arm, hlaw]

/-- The unstructured product class in Theorem 16.2: each arm law belongs to
its specified component class. Finite means are certified by the environment. -/
def FiniteMeanBanditEnvironment.InUnstructuredClass
    {K : Nat} (environment : FiniteMeanBanditEnvironment K)
    (componentClass : Fin K → Set (Measure Real)) : Prop :=
  ∀ arm, environment.armLaw arm ∈ componentClass arm

/-- Replace one arm by a finite-mean probability law whose mean exceeds the
old optimum. This constructs the source alternative environment explicitly. -/
def FiniteMeanBanditEnvironment.withImprovedArm
    {K : Nat} (environment : FiniteMeanBanditEnvironment K)
    (changedArm : Fin K) (alternative : Measure Real)
    [IsProbabilityMeasure alternative] (hintegrable : Integrable id alternative)
    (hbetter : environment.mean environment.bestArm < ∫ x, x ∂alternative) :
    FiniteMeanBanditEnvironment K where
  armLaw := Kernel.ofFunOfCountable
    (fun arm => if arm = changedArm then alternative else environment.armLaw arm)
  armLaw_isMarkov := ⟨by
    intro arm
    change IsProbabilityMeasure
      (if arm = changedArm then alternative else environment.armLaw arm)
    split <;> infer_instance⟩
  mean := fun arm => if arm = changedArm then ∫ x, x ∂alternative else environment.mean arm
  integrable_id := by
    intro arm
    change Integrable id
      (if arm = changedArm then alternative else environment.armLaw arm)
    split
    · exact hintegrable
    · exact environment.integrable_id arm
  mean_eq_integral := by
    intro arm
    change (if arm = changedArm then ∫ x, x ∂alternative else environment.mean arm) =
      ∫ x, x ∂(if arm = changedArm then alternative else environment.armLaw arm)
    split
    · rfl
    · exact environment.mean_eq_integral arm
  bestArm := changedArm
  isBest := by
    intro arm
    simp only [ite_true]
    split
    · exact le_rfl
    · exact (environment.isBest arm).trans hbetter.le

@[simp]
theorem FiniteMeanBanditEnvironment.withImprovedArm_law
    {K : Nat} (environment : FiniteMeanBanditEnvironment K)
    (changedArm : Fin K) (alternative : Measure Real)
    [IsProbabilityMeasure alternative] (hi : Integrable id alternative)
    (hb : environment.mean environment.bestArm < ∫ x, x ∂alternative)
    (arm : Fin K) :
    (environment.withImprovedArm changedArm alternative hi hb).armLaw arm =
      if arm = changedArm then alternative else environment.armLaw arm := rfl

/-- The replacement arm is uniquely optimal, as required by Lemma 16.3. -/
theorem FiniteMeanBanditEnvironment.withImprovedArm_unique
    {K : Nat} (environment : FiniteMeanBanditEnvironment K)
    (changedArm : Fin K) (alternative : Measure Real)
    [IsProbabilityMeasure alternative] (hi : Integrable id alternative)
    (hb : environment.mean environment.bestArm < ∫ x, x ∂alternative)
    (arm : Fin K) (hne : arm ≠ changedArm) :
    (environment.withImprovedArm changedArm alternative hi hb).mean arm <
      (environment.withImprovedArm changedArm alternative hi hb).mean changedArm := by
  simp only [withImprovedArm, hne, ite_false, ite_true]
  exact (environment.isBest arm).trans_lt hb

/-- Unstructured classes permit exactly the single-component replacement
used by the source change-of-measure argument. -/
theorem FiniteMeanBanditEnvironment.withImprovedArm_mem
    {K : Nat} (environment : FiniteMeanBanditEnvironment K)
    (componentClass : Fin K → Set (Measure Real))
    (hclass : environment.InUnstructuredClass componentClass)
    (changedArm : Fin K) (alternative : Measure Real)
    [IsProbabilityMeasure alternative] (hi : Integrable id alternative)
    (hb : environment.mean environment.bestArm < ∫ x, x ∂alternative)
    (halt : alternative ∈ componentClass changedArm) :
    (environment.withImprovedArm changedArm alternative hi hb).InUnstructuredClass
      componentClass := by
  intro arm
  rw [withImprovedArm_law]
  split_ifs with h
  · simpa only [h] using halt
  · exact hclass arm

/-- The source identity behind Lemma 16.3:
`lambda - Delta_i(nu) = mu_i(nu') - muStar(nu)`. -/
theorem oneArmMeanIncrease_sub_gap_eq_changedMargin
    {K : Nat} (original reference : FiniteMeanBanditEnvironment K)
    (changedArm : Fin K) :
    oneArmMeanIncrease original reference changedArm -
        original.gap changedArm =
      oneArmChangedMargin original reference changedArm := by
  simp only [oneArmMeanIncrease, oneArmChangedMargin,
    FiniteMeanBanditEnvironment.gap]
  ring

/-- Source mean-to-gap producer for a one-arm change.  If the changed arm is
suboptimal originally, uniquely optimal after the change, and every other arm
law is unchanged, then it produces all sign and comparison obligations needed
by the exact majority-event consumer for Lemma 16.3. -/
theorem oneArmMeanChange_produces_gap_contract
    {K : Nat} (original reference : FiniteMeanBanditEnvironment K)
    (changedArm : Fin K)
    (hsuboptimal :
      original.mean changedArm < original.mean original.bestArm)
    (hunique : forall arm, arm ≠ changedArm ->
      reference.mean arm < reference.mean changedArm)
    (hsame : forall arm, arm ≠ changedArm ->
      original.armLaw arm = reference.armLaw arm) :
    0 < original.gap changedArm /\
      0 < oneArmChangedMargin original reference changedArm /\
      (forall arm, arm ≠ changedArm ->
        oneArmChangedMargin original reference changedArm <=
          reference.gap arm) := by
  have hbest_ne : original.bestArm ≠ changedArm := by
    intro heq
    rw [heq] at hsuboptimal
    exact (lt_irrefl _ hsuboptimal)
  have hbest_mean :
      original.mean original.bestArm = reference.mean original.bestArm :=
    FiniteMeanBanditEnvironment.mean_eq_of_armLaw_eq
      original reference original.bestArm (hsame original.bestArm hbest_ne)
  have hchangedAbove :
      original.mean original.bestArm < reference.mean changedArm := by
    rw [hbest_mean]
    exact hunique original.bestArm hbest_ne
  have hrefBest : reference.bestArm = changedArm := by
    by_contra hne
    have hlt := hunique reference.bestArm hne
    have hle := reference.isBest changedArm
    exact (not_lt_of_ge hle) hlt
  refine ⟨?_, ?_, ?_⟩
  · exact sub_pos.mpr hsuboptimal
  · exact sub_pos.mpr hchangedAbove
  · intro arm harm
    have hmean := FiniteMeanBanditEnvironment.mean_eq_of_armLaw_eq
      original reference arm (hsame arm harm)
    rw [oneArmChangedMargin, FiniteMeanBanditEnvironment.gap,
      hrefBest, ← hmean]
    linarith [original.isBest arm]

/-- An unrestricted finite vector of unit-variance Gaussian means, together
with a certified optimal arm.  Unlike the Chapter 15 minimax cube, Chapter 16
uses all mean vectors in `Real^k`. -/
structure UnitVarianceGaussianBanditEnvironment (K : Nat) where
  mean : Fin K -> Real
  bestArm : Fin K
  isBest : forall arm, mean arm <= mean bestArm

def UnitVarianceGaussianBanditEnvironment.gap
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (arm : Fin K) : Real :=
  environment.mean environment.bestArm - environment.mean arm

theorem UnitVarianceGaussianBanditEnvironment.gap_nonneg
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (arm : Fin K) :
    0 <= environment.gap arm := by
  exact sub_nonneg.mpr (environment.isBest arm)

/-- The finite-mean product environment induced by arbitrary unit-variance
Gaussian arms. -/
noncomputable def UnitVarianceGaussianBanditEnvironment.toFiniteMean
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K) :
    FiniteMeanBanditEnvironment K where
  armLaw := unitGaussianKernel environment.mean
  armLaw_isMarkov := inferInstance
  mean := environment.mean
  integrable_id := by
    intro arm
    change Integrable id (gaussianReal (environment.mean arm) (1 : NNReal))
    apply integrable_of_mem_interior_integrableExpSet
    simp
  mean_eq_integral := by
    intro arm
    simp
  bestArm := environment.bestArm
  isBest := environment.isBest

@[simp]
theorem UnitVarianceGaussianBanditEnvironment.toFiniteMean_mean
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K) :
    environment.toFiniteMean.mean = environment.mean := rfl

@[simp]
theorem UnitVarianceGaussianBanditEnvironment.toFiniteMean_gap
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K) :
    environment.toFiniteMean.gap = environment.gap := rfl

/-- Mean vector obtained by increasing exactly one Gaussian arm by
`(1 + epsilon) Delta_i`, as in the proof of Theorem 16.4. -/
def chapter16GaussianChangedMean
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon : Real) (arm : Fin K) : Real :=
  if arm = changedArm then
    environment.mean changedArm +
      (1 + epsilon) * environment.gap changedArm
  else environment.mean arm

@[simp]
theorem chapter16GaussianChangedMean_changed
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon : Real) :
    chapter16GaussianChangedMean environment changedArm epsilon changedArm =
      environment.mean changedArm +
        (1 + epsilon) * environment.gap changedArm := by
  simp [chapter16GaussianChangedMean]

theorem chapter16GaussianChangedMean_other
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon : Real)
    (arm : Fin K) (harm : arm ≠ changedArm) :
    chapter16GaussianChangedMean environment changedArm epsilon arm =
      environment.mean arm := by
  simp [chapter16GaussianChangedMean, harm]

/-- The shifted Gaussian arm is uniquely optimal whenever its original gap
and `epsilon` are positive. -/
theorem chapter16GaussianChangedMean_uniqueBest
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon : Real)
    (hgap : 0 < environment.gap changedArm)
    (hepsilon : 0 < epsilon) :
    forall arm, arm ≠ changedArm ->
      chapter16GaussianChangedMean environment changedArm epsilon arm <
        chapter16GaussianChangedMean environment changedArm epsilon changedArm := by
  intro arm harm
  rw [chapter16GaussianChangedMean_other environment changedArm epsilon arm harm,
    chapter16GaussianChangedMean_changed]
  dsimp [UnitVarianceGaussianBanditEnvironment.gap] at hgap ⊢
  have hbest := environment.isBest arm
  nlinarith

/-- The shifted mean vector, certified with the changed arm as an optimum. -/
noncomputable def chapter16GaussianChangedEnvironment
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon : Real)
    (hgap : 0 < environment.gap changedArm)
    (hepsilon : 0 < epsilon) :
    UnitVarianceGaussianBanditEnvironment K where
  mean := chapter16GaussianChangedMean environment changedArm epsilon
  bestArm := changedArm
  isBest := by
    intro arm
    by_cases harm : arm = changedArm
    · simp [harm]
    · exact (chapter16GaussianChangedMean_uniqueBest
        environment changedArm epsilon hgap hepsilon arm harm).le

/-- The Gaussian shift stays in the source box
`[mu_j, mu_j + 2 Delta_j]` when `epsilon <= 1`. -/
theorem chapter16GaussianChangedMean_mem_localBox
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon : Real)
    (hgap : 0 < environment.gap changedArm)
    (hepsilon : 0 < epsilon) (hepsilon_one : epsilon <= 1) :
    forall arm,
      chapter16GaussianChangedMean environment changedArm epsilon arm ∈
        Set.Icc (environment.mean arm)
          (environment.mean arm + 2 * environment.gap arm) := by
  intro arm
  by_cases harm : arm = changedArm
  · subst arm
    rw [chapter16GaussianChangedMean_changed]
    constructor <;> nlinarith
  · rw [chapter16GaussianChangedMean_other environment changedArm epsilon arm harm]
    constructor
    · exact le_rfl
    · nlinarith [environment.gap_nonneg arm]

theorem chapter16GaussianChangedEnvironment_uniqueBest
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon : Real)
    (hgap : 0 < environment.gap changedArm)
    (hepsilon : 0 < epsilon) :
    forall arm, arm ≠ changedArm ->
      (chapter16GaussianChangedEnvironment environment changedArm epsilon
        hgap hepsilon).mean arm <
      (chapter16GaussianChangedEnvironment environment changedArm epsilon
        hgap hepsilon).mean changedArm := by
  exact chapter16GaussianChangedMean_uniqueBest
    environment changedArm epsilon hgap hepsilon

theorem chapter16GaussianChangedEnvironment_sameArmLaw
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon : Real)
    (hgap : 0 < environment.gap changedArm)
    (hepsilon : 0 < epsilon) :
    forall arm, arm ≠ changedArm ->
      environment.toFiniteMean.armLaw arm =
        (chapter16GaussianChangedEnvironment environment changedArm epsilon
          hgap hepsilon).toFiniteMean.armLaw arm := by
  intro arm harm
  simp only [UnitVarianceGaussianBanditEnvironment.toFiniteMean,
    unitGaussianKernel_apply]
  change unitGaussianArm (environment.mean arm) =
    unitGaussianArm
      (chapter16GaussianChangedMean environment changedArm epsilon arm)
  rw [chapter16GaussianChangedMean_other environment changedArm epsilon arm harm]

theorem chapter16GaussianChangedEnvironment_meanIncrease
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon : Real)
    (hgap : 0 < environment.gap changedArm)
    (hepsilon : 0 < epsilon) :
    oneArmMeanIncrease environment.toFiniteMean
        (chapter16GaussianChangedEnvironment environment changedArm epsilon
          hgap hepsilon).toFiniteMean changedArm =
      (1 + epsilon) * environment.gap changedArm := by
  simp [oneArmMeanIncrease, chapter16GaussianChangedEnvironment,
    chapter16GaussianChangedMean]

theorem chapter16GaussianChangedEnvironment_changedMargin
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon : Real)
    (hgap : 0 < environment.gap changedArm)
    (hepsilon : 0 < epsilon) :
    oneArmChangedMargin environment.toFiniteMean
        (chapter16GaussianChangedEnvironment environment changedArm epsilon
          hgap hepsilon).toFiniteMean changedArm =
      epsilon * environment.gap changedArm := by
  simp [oneArmChangedMargin, chapter16GaussianChangedEnvironment,
    chapter16GaussianChangedMean,
    UnitVarianceGaussianBanditEnvironment.toFiniteMean,
    UnitVarianceGaussianBanditEnvironment.gap]
  ring

theorem chapter16GaussianChangedEnvironment_armKL
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon : Real)
    (hgap : 0 < environment.gap changedArm)
    (hepsilon : 0 < epsilon) :
    InformationTheory.klDiv
      (environment.toFiniteMean.armLaw changedArm)
      ((chapter16GaussianChangedEnvironment environment changedArm epsilon
        hgap hepsilon).toFiniteMean.armLaw changedArm) =
      ENNReal.ofReal (((1 + epsilon) * environment.gap changedArm) ^ 2 / 2) := by
  simp only [UnitVarianceGaussianBanditEnvironment.toFiniteMean,
    unitGaussianKernel_apply, chapter16GaussianChangedEnvironment,
    chapter16GaussianChangedMean_changed]
  rw [klDiv_gaussianReal_one]
  congr 1
  ring

theorem chapter16GaussianChangedEnvironment_armKL_toReal
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon : Real)
    (hgap : 0 < environment.gap changedArm)
    (hepsilon : 0 < epsilon) :
    (InformationTheory.klDiv
      (environment.toFiniteMean.armLaw changedArm)
      ((chapter16GaussianChangedEnvironment environment changedArm epsilon
        hgap hepsilon).toFiniteMean.armLaw changedArm)).toReal =
      ((1 + epsilon) * environment.gap changedArm) ^ 2 / 2 := by
  rw [chapter16GaussianChangedEnvironment_armKL]
  rw [ENNReal.toReal_ofReal]
  positivity

/-- Membership in the local Gaussian class `E(nu)` of Theorem 16.4. -/
def InChapter16GaussianLocalClass
    {K : Nat} (base candidate : UnitVarianceGaussianBanditEnvironment K) : Prop :=
  forall arm, candidate.mean arm ∈
    Set.Icc (base.mean arm) (base.mean arm + 2 * base.gap arm)

theorem inChapter16GaussianLocalClass_self
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K) :
    InChapter16GaussianLocalClass environment environment := by
  intro arm
  constructor
  · exact le_rfl
  · nlinarith [environment.gap_nonneg arm]

theorem inChapter16GaussianLocalClass_changed
    {K : Nat} (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon : Real)
    (hgap : 0 < environment.gap changedArm)
    (hepsilon : 0 < epsilon) (hepsilon_one : epsilon <= 1) :
    InChapter16GaussianLocalClass environment
      (chapter16GaussianChangedEnvironment environment changedArm epsilon
        hgap hepsilon) :=
  chapter16GaussianChangedMean_mem_localBox
    environment changedArm epsilon hgap hepsilon hepsilon_one

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

/-- Consistency extracts every strict reciprocal-information lower bound
from the source logarithmic inequality. This eventual form does not assume
that the normalized pull counts converge. -/
theorem IsConsistentRegret.eventually_pull_div_log_ge
    {first second pulls : Nat → Real} {c d r : Real}
    (hfirst : IsConsistentRegret first) (hsecond : IsConsistentRegret second)
    (hpositive : ∀ᶠ n in atTop, 0 < first n + second n)
    (hd : 0 < d) (hr : r < 1 / d)
    (hsource : ∀ᶠ n : Nat in atTop,
      (c + Real.log n - Real.log (first n + second n)) / d ≤ pulls n) :
    ∀ᶠ n in atTop, r ≤ pulls n / Real.log n := by
  let p : Real := (1 - r * d) / 2
  have hrd : r * d < 1 := (lt_div_iff₀ hd).mp hr
  have hp : 0 < p := by dsimp [p]; linarith
  have hrp : r < (1 - p) / d := by
    apply (lt_div_iff₀ hd).2
    dsimp [p]
    linarith
  have hlogtop : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconstant : Tendsto (fun n : Nat => c / Real.log n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlogtop
  have hlimit : Tendsto (fun n : Nat => (c / Real.log n + 1 - p) / d)
      atTop (nhds ((1 - p) / d)) := by
    simpa using ((hconstant.add_const 1).sub_const p).div_const d
  have hevent := hlimit.eventually_const_lt hrp
  filter_upwards [hevent, hsource,
    hfirst.eventually_log_add_div_log_le hsecond hpositive hp,
    eventually_gt_atTop (1 : Nat)] with n hn hs hg hnlarge
  have hnreal : (1 : Real) < n := by exact_mod_cast hnlarge
  have hlog : 0 < Real.log (n : Real) := Real.log_pos hnreal
  apply hn.le.trans
  apply (div_le_iff₀ hd).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlog).2
  have hc : c / Real.log n * Real.log n = c := div_mul_cancel₀ c hlog.ne'
  have hs' := (div_le_iff₀ hd).mp hs
  have hg' := (div_le_iff₀ hlog).mp hg
  nlinarith

/-- The finite-positive information branch in extended-real liminf form.
The conclusion allows infinite normalized pull growth. -/
theorem IsConsistentRegret.liminf_pull_div_log_ge
    {first second pulls : Nat → Real} {c d : Real}
    (hfirst : IsConsistentRegret first) (hsecond : IsConsistentRegret second)
    (hpositive : ∀ᶠ n in atTop, 0 < first n + second n)
    (hd : 0 < d)
    (hsource : ∀ᶠ n : Nat in atTop,
      (c + Real.log n - Real.log (first n + second n)) / d ≤ pulls n) :
    ENNReal.ofReal (1 / d) ≤
      liminf (fun n : Nat => ENNReal.ofReal (pulls n / Real.log n)) atTop := by
  apply (le_liminf_iff' (by isBoundedDefault) (by isBoundedDefault)).2
  intro bound hbound
  have hr := ENNReal.toReal_lt_of_lt_ofReal hbound
  filter_upwards [hfirst.eventually_pull_div_log_ge hsecond hpositive hd hr hsource]
    with n hn
  calc
    bound = ENNReal.ofReal bound.toReal := (ENNReal.ofReal_toReal hbound.ne_top).symm
    _ ≤ ENNReal.ofReal (pulls n / Real.log n) := ENNReal.ofReal_le_ofReal hn

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

/-- Every strict upper bound on `d_inf` admits a confusing alternative below
that bound. No minimizer or finite positive infimum is assumed. -/
theorem divergenceInfimum_exists_alternative_lt
    {Reward : Type*} [MeasurableSpace Reward]
    {P : Measure Reward} {muStar : Real}
    {distributionClass : Set (Measure Reward)}
    {mean : Measure Reward -> Real} {bound : ENNReal}
    (hbound : divergenceInfimum P muStar distributionClass mean < bound) :
    ∃ P', P' ∈ distributionClass ∧ muStar < mean P' ∧
      relativeEntropy P P' < bound := by
  by_contra h
  push_neg at h
  have hlower : bound ≤ divergenceInfimum P muStar distributionClass mean := by
    apply le_sInf
    rintro cost ⟨P', hclass, hbetter, rfl⟩
    exact h P' hclass hbetter
  exact (not_le_of_gt hbound) hlower

/-- Lift a near-infimum arm law to an admissible product environment. The
component classes consist of finite-mean probability laws, exactly as in
Theorem 16.2; the information cost stays in `ENNReal`. -/
theorem FiniteMeanBanditEnvironment.exists_confusingEnvironment_lt
    {K : Nat} (environment : FiniteMeanBanditEnvironment K)
    (componentClass : Fin K → Set (Measure Real))
    (hclass : environment.InUnstructuredClass componentClass)
    (hfinite : ∀ arm P, P ∈ componentClass arm →
      IsProbabilityMeasure P ∧ Integrable id P)
    (changedArm : Fin K) {bound : ENNReal}
    (hbound : divergenceInfimum (environment.armLaw changedArm)
      (environment.mean environment.bestArm) (componentClass changedArm)
      (fun P => ∫ x, x ∂P) < bound) :
    ∃ reference : FiniteMeanBanditEnvironment K,
      reference.InUnstructuredClass componentClass ∧
      (∀ arm, arm ≠ changedArm → environment.armLaw arm = reference.armLaw arm) ∧
      (∀ arm, arm ≠ changedArm → reference.mean arm < reference.mean changedArm) ∧
      relativeEntropy (environment.armLaw changedArm) (reference.armLaw changedArm) < bound := by
  obtain ⟨alternative, halt, hbetter, hcost⟩ :=
    divergenceInfimum_exists_alternative_lt hbound
  obtain ⟨hprob, hi⟩ := hfinite changedArm alternative halt
  letI : IsProbabilityMeasure alternative := hprob
  refine ⟨environment.withImprovedArm changedArm alternative hi hbetter,
    environment.withImprovedArm_mem componentClass hclass changedArm alternative hi hbetter halt,
    ?_, ?_, ?_⟩
  · intro arm hne
    simp only [withImprovedArm_law, hne, ite_false]
  · intro arm hne
    exact environment.withImprovedArm_unique changedArm alternative hi hbetter arm hne
  · simpa only [withImprovedArm_law, ite_true] using hcost

/-- The infinite branch includes both an empty alternative class and classes
whose every confusing alternative has infinite directed KL. -/
theorem divergenceInfimum_eq_top_iff
    {Reward : Type*} [MeasurableSpace Reward]
    {P : Measure Reward} {muStar : Real}
    {distributionClass : Set (Measure Reward)}
    {mean : Measure Reward -> Real} :
    divergenceInfimum P muStar distributionClass mean = ⊤ ↔
      ∀ P', P' ∈ distributionClass → muStar < mean P' →
        relativeEntropy P P' = ⊤ := by
  constructor
  · intro hinf P' hclass hbetter
    apply top_unique
    rw [← hinf]
    exact divergenceInfimum_le hclass hbetter
  · intro h
    apply top_unique
    apply le_sInf
    rintro cost ⟨P', hclass, hbetter, rfl⟩
    exact le_of_eq (h P' hclass hbetter).symm

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

/-- Every strictly better unit-Gaussian alternative costs at least the
boundary value from Table 16.1. -/
theorem unitGaussianDivergenceInfimum_ge
    (mu muStar : Real) (hmu : mu < muStar) :
    ENNReal.ofReal ((muStar - mu) ^ 2 / 2) <=
      unitGaussianDivergenceInfimum mu muStar := by
  apply le_sInf
  intro cost hcost
  rcases hcost with ⟨alternative, hbetter, rfl⟩
  change muStar < alternative at hbetter
  change ENNReal.ofReal ((muStar - mu) ^ 2 / 2) <=
    InformationTheory.klDiv (unitGaussianArm mu)
      (unitGaussianArm alternative)
  rw [klDiv_gaussianReal_one]
  apply ENNReal.ofReal_le_ofReal
  have hbase : 0 <= muStar - mu := sub_nonneg.mpr hmu.le
  have halternative : 0 <= alternative - mu :=
    sub_nonneg.mpr (hmu.trans hbetter).le
  have hdistance : muStar - mu <= alternative - mu := by linarith
  have hsquare : (muStar - mu) ^ 2 <= (alternative - mu) ^ 2 :=
    (sq_le_sq₀ hbase halternative).2 hdistance
  nlinarith [hsquare]

/-- Exact unit-variance Gaussian row of Table 16.1.  The strict alternative
mean means the boundary law is not itself admissible; the reverse inequality
is obtained from positive perturbations tending to zero. -/
theorem unitGaussianDivergenceInfimum_eq
    (mu muStar : Real) (hmu : mu < muStar) :
    unitGaussianDivergenceInfimum mu muStar =
      ENNReal.ofReal ((muStar - mu) ^ 2 / 2) := by
  apply le_antisymm
  · have hinv : Tendsto (fun n : Nat => 1 / ((n + 1 : Nat) : Real))
        atTop (nhds 0) := by
      convert
        (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := Real) 1).comp
          (tendsto_add_atTop_nat 1) using 1
    have hreal : Tendsto
        (fun n : Nat =>
          (((muStar - mu) + 1 / ((n + 1 : Nat) : Real)) ^ 2 / 2))
        atTop (nhds ((muStar - mu) ^ 2 / 2)) := by
      simpa using ((tendsto_const_nhds.add hinv).pow 2).div_const (2 : Real)
    have hennreal : Tendsto
        (fun n : Nat => ENNReal.ofReal
          (((muStar - mu) + 1 / ((n + 1 : Nat) : Real)) ^ 2 / 2))
        atTop (nhds (ENNReal.ofReal ((muStar - mu) ^ 2 / 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hreal
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hennreal fun n =>
      unitGaussianDivergenceInfimum_le_perturbed
        mu muStar (1 / ((n + 1 : Nat) : Real)) (by positivity)
  · exact unitGaussianDivergenceInfimum_ge mu muStar hmu

/-- Chapter 16's one-arm change-of-measure specialization of Lemma 15.1.
When two stationary bandit environments differ only at `changedArm`, the
directed relative entropy of their finite histories is exactly the
first-environment expected number of pulls of that arm times its arm-law
relative entropy.  The algorithm is one common, possibly randomized,
nonanticipating history policy in both environments. -/
theorem banditHistoryRelativeEntropy_eq_expectedPulls_mul_of_only_arm_changed
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (changedArm : Fin K) (lastRound : Nat)
    (hsame : forall arm, arm ≠ changedArm ->
      armLaw arm = referenceArmLaw arm) :
    InformationTheory.klDiv
        (canonicalBanditHistoryMeasure algorithm armLaw lastRound)
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound) =
      canonicalRealizedExpectedPullCountThrough
          algorithm armLaw lastRound changedArm *
        InformationTheory.klDiv
          (armLaw changedArm) (referenceArmLaw changedArm) := by
  classical
  rw [banditHistoryRelativeEntropy_eq_expectedPulls_sum]
  apply Finset.sum_eq_single changedArm
  · intro arm _harm hne
    rw [hsame arm hne, InformationTheory.klDiv_self, mul_zero]
  · simp

/-- The source majority event `A = {T_i(n) > n/2}` in the repository's
inclusive convention, where `lastRound` contains `lastRound + 1` pulls. -/
def oneArmMajorityPullEvent
    {K : Nat} {Reward : Type*}
    (changedArm : Fin K) (lastRound : Nat) :
    Set (History.FinitePairHistory (Fin K) Reward lastRound) :=
  {history |
    (lastRound + 1 : ENNReal) <
      2 * finiteHistoryPullCountENNReal lastRound history changedArm}

theorem measurableSet_oneArmMajorityPullEvent
    {K : Nat} {Reward : Type*} [MeasurableSpace Reward]
    (changedArm : Fin K) (lastRound : Nat) :
    MeasurableSet
      (oneArmMajorityPullEvent (Reward := Reward) changedArm lastRound) := by
  exact measurableSet_lt measurable_const
    (measurable_const.mul
      (measurable_finiteHistoryPullCountENNReal lastRound changedArm))

/-- Gap-times-pull-count pseudo-regret on one realized finite history.  The
gap vector is kept explicit so the later Chapter 16 environment layer must
identify it with `muStar - mu_i`; no scalar regret hypothesis is hidden here. -/
noncomputable def finiteHistoryGapPseudoRegret
    {K : Nat} {Reward : Type*}
    (gap : Fin K -> Real) (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Reward lastRound) : ENNReal :=
  ∑ arm : Fin K,
    ENNReal.ofReal (gap arm) *
      finiteHistoryPullCountENNReal lastRound history arm

/-- Expected gap pseudo-regret under the canonical law generated by one
possibly randomized history policy and one stationary arm kernel. -/
noncomputable def canonicalGapExpectedPseudoRegret
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (gap : Fin K -> Real) (lastRound : Nat) : ENNReal :=
  ∫⁻ history,
    finiteHistoryGapPseudoRegret gap lastRound history
    ∂canonicalBanditHistoryMeasure algorithm armLaw lastRound

theorem measurable_finiteHistoryGapPseudoRegret
    {K : Nat} {Reward : Type*} [MeasurableSpace Reward]
    (gap : Fin K -> Real) (lastRound : Nat) :
    Measurable (finiteHistoryGapPseudoRegret
      (Reward := Reward) gap lastRound) := by
  classical
  unfold finiteHistoryGapPseudoRegret
  exact Finset.measurable_sum Finset.univ fun arm _harm =>
    measurable_const.mul
      (measurable_finiteHistoryPullCountENNReal lastRound arm)

theorem finiteHistoryGapPseudoRegret_ne_top
    {K : Nat} {Reward : Type*}
    (gap : Fin K -> Real) (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Reward lastRound) :
    finiteHistoryGapPseudoRegret gap lastRound history ≠ ∞ := by
  classical
  unfold finiteHistoryGapPseudoRegret
  exact ENNReal.sum_ne_top.mpr fun arm _harm =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (finiteHistoryPullCountENNReal_ne_top lastRound history arm)

theorem finiteHistoryGapPseudoRegret_toReal
    {K : Nat} {Reward : Type*}
    (gap : Fin K -> Real) (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Reward lastRound)
    (hgap : forall arm, 0 <= gap arm) :
    (finiteHistoryGapPseudoRegret gap lastRound history).toReal =
      ∑ arm : Fin K,
        gap arm * finiteHistoryPullCountReal lastRound history arm := by
  classical
  unfold finiteHistoryGapPseudoRegret
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro arm _harm
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hgap arm)]
    rfl
  · intro arm _harm
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (finiteHistoryPullCountENNReal_ne_top lastRound history arm)

/-- The expected realized pull counts of all arms sum to the inclusive horizon
for every Markov arm kernel, not only for the Gaussian Chapter 15 instance. -/
theorem sum_canonicalRealizedExpectedPullCountThrough_general
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (lastRound : Nat) :
    ∑ arm : Fin K,
        canonicalRealizedExpectedPullCountThrough
          algorithm armLaw lastRound arm = lastRound + 1 := by
  classical
  unfold canonicalRealizedExpectedPullCountThrough
  rw [← MeasureTheory.lintegral_finset_sum]
  · simp_rw [sum_finiteHistoryPullCountENNReal]
    simp
  · intro arm _harm
    exact measurable_finiteHistoryPullCountENNReal lastRound arm

theorem canonicalRealizedExpectedPullCountThrough_ne_top
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (lastRound : Nat) (arm : Fin K) :
    canonicalRealizedExpectedPullCountThrough
      algorithm armLaw lastRound arm ≠ ∞ := by
  have hle : canonicalRealizedExpectedPullCountThrough
      algorithm armLaw lastRound arm <=
      ∑ other : Fin K,
        canonicalRealizedExpectedPullCountThrough
          algorithm armLaw lastRound other :=
    Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ arm)
  rw [sum_canonicalRealizedExpectedPullCountThrough_general] at hle
  exact ne_top_of_le_ne_top (by simp) hle

theorem canonicalGapExpectedPseudoRegret_eq_sum_expectedPulls
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (gap : Fin K -> Real) (lastRound : Nat) :
    canonicalGapExpectedPseudoRegret algorithm armLaw gap lastRound =
      ∑ arm : Fin K,
        ENNReal.ofReal (gap arm) *
          canonicalRealizedExpectedPullCountThrough
            algorithm armLaw lastRound arm := by
  classical
  unfold canonicalGapExpectedPseudoRegret finiteHistoryGapPseudoRegret
  rw [MeasureTheory.lintegral_finset_sum]
  · apply Finset.sum_congr rfl
    intro arm _harm
    rw [MeasureTheory.lintegral_const_mul _
      (measurable_finiteHistoryPullCountENNReal lastRound arm)]
    rfl
  · intro arm _harm
    exact measurable_const.mul
      (measurable_finiteHistoryPullCountENNReal lastRound arm)

theorem canonicalGapExpectedPseudoRegret_ne_top
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (gap : Fin K -> Real) (lastRound : Nat) :
    canonicalGapExpectedPseudoRegret algorithm armLaw gap lastRound ≠ ∞ := by
  rw [canonicalGapExpectedPseudoRegret_eq_sum_expectedPulls]
  exact ENNReal.sum_ne_top.mpr fun arm _harm =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (canonicalRealizedExpectedPullCountThrough_ne_top
        algorithm armLaw lastRound arm)

/-- Real-valued presentation of the finite expected pseudo-regret.  Finiteness
is proved above rather than assumed by the Chapter 16 consumer. -/
noncomputable def canonicalGapExpectedPseudoRegretReal
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (gap : Fin K -> Real) (lastRound : Nat) : Real :=
  (canonicalGapExpectedPseudoRegret algorithm armLaw gap lastRound).toReal

/-- Real-valued gap-times-expected-pulls decomposition.  This is the precise
finite-horizon form used when Theorem 16.4 sums its per-arm lower bounds. -/
theorem canonicalGapExpectedPseudoRegretReal_eq_sum_expectedPulls
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (gap : Fin K -> Real) (hgap : forall arm, 0 <= gap arm)
    (lastRound : Nat) :
    canonicalGapExpectedPseudoRegretReal algorithm armLaw gap lastRound =
      ∑ arm : Fin K, gap arm *
        (canonicalRealizedExpectedPullCountThrough
          algorithm armLaw lastRound arm).toReal := by
  classical
  unfold canonicalGapExpectedPseudoRegretReal
  rw [canonicalGapExpectedPseudoRegret_eq_sum_expectedPulls,
    ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro arm _harm
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hgap arm)]
  · intro arm _harm
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (canonicalRealizedExpectedPullCountThrough_ne_top
        algorithm armLaw lastRound arm)

/-- Expected pseudo-regret of an unrestricted unit-variance Gaussian
environment in the Chapter 16 gap-times-pulls convention. -/
noncomputable def unitVarianceGaussianExpectedPseudoRegret
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : UnitVarianceGaussianBanditEnvironment K)
    (lastRound : Nat) : Real :=
  canonicalGapExpectedPseudoRegretReal algorithm
    (unitGaussianKernel environment.mean) environment.gap lastRound

/-- On the source majority event, the original environment pays at least half
the horizon times the changed arm's positive gap. -/
theorem oneArmMajority_forces_gapPseudoRegret
    {K : Nat} {Reward : Type*}
    (gap : Fin K -> Real) (hgap : forall arm, 0 <= gap arm)
    (changedArm : Fin K) (hchanged : 0 < gap changedArm)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Reward lastRound)
    (hA : history ∈ oneArmMajorityPullEvent
      (Reward := Reward) changedArm lastRound) :
    ENNReal.ofReal
        (((lastRound + 1 : Nat) : Real) * gap changedArm / 2) <=
      finiteHistoryGapPseudoRegret gap lastRound history := by
  apply (ENNReal.ofReal_le_iff_le_toReal
    (finiteHistoryGapPseudoRegret_ne_top gap lastRound history)).mpr
  rw [finiteHistoryGapPseudoRegret_toReal gap lastRound history hgap]
  have hsingle := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin K)))
    (f := fun arm => gap arm *
      finiteHistoryPullCountReal lastRound history arm)
    (fun arm _harm => mul_nonneg (hgap arm)
      (finiteHistoryPullCountReal_nonneg lastRound history arm))
    (Finset.mem_univ changedArm)
  have hAreal : ((lastRound + 1 : Nat) : Real) <
      2 * finiteHistoryPullCountReal lastRound history changedArm := by
    have hconverted := (ENNReal.toReal_lt_toReal
      (by simp : (lastRound + 1 : ENNReal) ≠ ∞)
      (ENNReal.mul_ne_top (by simp)
        (finiteHistoryPullCountENNReal_ne_top
          lastRound history changedArm))).2 hA
    simpa [finiteHistoryPullCountReal] using hconverted
  nlinarith

/-- On the complement of the majority event, every non-changed arm charged by
at least `changedMargin` forces half-horizon pseudo-regret. -/
theorem oneArmMajority_compl_forces_gapPseudoRegret
    {K : Nat} {Reward : Type*}
    (gap : Fin K -> Real) (hgap : forall arm, 0 <= gap arm)
    (changedArm : Fin K) (changedMargin : Real)
    (hmargin : 0 < changedMargin)
    (hother : forall arm, arm ≠ changedArm -> changedMargin <= gap arm)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Reward lastRound)
    (hAc : history ∈ (oneArmMajorityPullEvent
      (Reward := Reward) changedArm lastRound)ᶜ) :
    ENNReal.ofReal
        (((lastRound + 1 : Nat) : Real) * changedMargin / 2) <=
      finiteHistoryGapPseudoRegret gap lastRound history := by
  apply (ENNReal.ofReal_le_iff_le_toReal
    (finiteHistoryGapPseudoRegret_ne_top gap lastRound history)).mpr
  rw [finiteHistoryGapPseudoRegret_toReal gap lastRound history hgap]
  have hnot : ¬ (lastRound + 1 : ENNReal) <
      2 * finiteHistoryPullCountENNReal lastRound history changedArm := by
    simpa [oneArmMajorityPullEvent] using hAc
  have hcountENN : 2 * finiteHistoryPullCountENNReal
      lastRound history changedArm <= lastRound + 1 := le_of_not_gt hnot
  have hcount : 2 * finiteHistoryPullCountReal
      lastRound history changedArm <= ((lastRound + 1 : Nat) : Real) := by
    have hconverted := ENNReal.toReal_mono
      (by simp : (lastRound + 1 : ENNReal) ≠ ∞) hcountENN
    simpa [finiteHistoryPullCountReal] using hconverted
  have htotal := sum_finiteHistoryPullCountReal lastRound history
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin K))
    (fun arm => finiteHistoryPullCountReal lastRound history arm)
    (Finset.mem_univ changedArm)
  have hotherCount :
      (∑ arm ∈ (Finset.univ : Finset (Fin K)).erase changedArm,
        finiteHistoryPullCountReal lastRound history arm) =
        ((lastRound + 1 : Nat) : Real) -
          finiteHistoryPullCountReal lastRound history changedArm := by
    norm_num [Nat.cast_add, Nat.cast_one] at htotal ⊢
  have hcharged :
      changedMargin *
          (∑ arm ∈ (Finset.univ : Finset (Fin K)).erase changedArm,
            finiteHistoryPullCountReal lastRound history arm) <=
        ∑ arm ∈ (Finset.univ : Finset (Fin K)).erase changedArm,
          gap arm * finiteHistoryPullCountReal lastRound history arm := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro arm harm
    exact mul_le_mul_of_nonneg_right
      (hother arm (by simpa using harm))
      (finiteHistoryPullCountReal_nonneg lastRound history arm)
  have hfull :
      (∑ arm ∈ (Finset.univ : Finset (Fin K)).erase changedArm,
          gap arm * finiteHistoryPullCountReal lastRound history arm) <=
        ∑ arm : Fin K,
          gap arm * finiteHistoryPullCountReal lastRound history arm := by
    have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin K))
      (fun arm => gap arm * finiteHistoryPullCountReal lastRound history arm)
      (Finset.mem_univ changedArm)
    rw [← hsum]
    exact le_add_of_nonneg_right
      (mul_nonneg (hgap changedArm)
        (finiteHistoryPullCountReal_nonneg lastRound history changedArm))
  rw [hotherCount] at hcharged
  refine le_trans ?_ (hcharged.trans hfull)
  nlinarith

/-- Original-environment event probability charged to the actual canonical
gap pseudo-regret. -/
theorem oneArmMajority_probability_charge_le_expectedPseudoRegret
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (gap : Fin K -> Real) (hgap : forall arm, 0 <= gap arm)
    (changedArm : Fin K) (hchanged : 0 < gap changedArm)
    (lastRound : Nat) :
    ((lastRound + 1 : Nat) : Real) * gap changedArm / 2 *
        (canonicalBanditHistoryMeasure algorithm armLaw lastRound).real
          (oneArmMajorityPullEvent (Reward := Reward)
            changedArm lastRound) <=
      canonicalGapExpectedPseudoRegretReal
        algorithm armLaw gap lastRound := by
  have hENN := ofReal_mul_probReal_le_lintegral_of_event
    (mu := canonicalBanditHistoryMeasure algorithm armLaw lastRound)
    (measurableSet_oneArmMajorityPullEvent
      (Reward := Reward) changedArm lastRound)
    (show 0 <= ((lastRound + 1 : Nat) : Real) * gap changedArm / 2 by
      positivity)
    (oneArmMajority_forces_gapPseudoRegret
      gap hgap changedArm hchanged lastRound)
  have hreal := ENNReal.toReal_mono
    (canonicalGapExpectedPseudoRegret_ne_top
      algorithm armLaw gap lastRound) hENN
  have hleft : 0 <=
      ((lastRound + 1 : Nat) : Real) * gap changedArm / 2 *
        (canonicalBanditHistoryMeasure algorithm armLaw lastRound).real
          (oneArmMajorityPullEvent (Reward := Reward)
            changedArm lastRound) := by positivity
  rw [ENNReal.toReal_ofReal hleft] at hreal
  simpa only [canonicalGapExpectedPseudoRegretReal] using hreal

/-- Changed-environment complement probability charged to the actual
canonical gap pseudo-regret. -/
theorem oneArmMajority_compl_probability_charge_le_expectedPseudoRegret
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw : Kernel (Fin K) Reward) [IsMarkovKernel armLaw]
    (gap : Fin K -> Real) (hgap : forall arm, 0 <= gap arm)
    (changedArm : Fin K) (changedMargin : Real)
    (hmargin : 0 < changedMargin)
    (hother : forall arm, arm ≠ changedArm -> changedMargin <= gap arm)
    (lastRound : Nat) :
    ((lastRound + 1 : Nat) : Real) * changedMargin / 2 *
        (canonicalBanditHistoryMeasure algorithm armLaw lastRound).real
          (oneArmMajorityPullEvent (Reward := Reward)
            changedArm lastRound)ᶜ <=
      canonicalGapExpectedPseudoRegretReal
        algorithm armLaw gap lastRound := by
  have hENN := ofReal_mul_probReal_le_lintegral_of_event
    (mu := canonicalBanditHistoryMeasure algorithm armLaw lastRound)
    (measurableSet_oneArmMajorityPullEvent
      (Reward := Reward) changedArm lastRound).compl
    (show 0 <= ((lastRound + 1 : Nat) : Real) * changedMargin / 2 by
      positivity)
    (oneArmMajority_compl_forces_gapPseudoRegret
      gap hgap changedArm changedMargin hmargin hother lastRound)
  have hreal := ENNReal.toReal_mono
    (canonicalGapExpectedPseudoRegret_ne_top
      algorithm armLaw gap lastRound) hENN
  have hleft : 0 <=
      ((lastRound + 1 : Nat) : Real) * changedMargin / 2 *
        (canonicalBanditHistoryMeasure algorithm armLaw lastRound).real
          (oneArmMajorityPullEvent (Reward := Reward)
            changedArm lastRound)ᶜ := by positivity
  rw [ENNReal.toReal_ofReal hleft] at hreal
  simpa only [canonicalGapExpectedPseudoRegretReal] using hreal

/-- Chapter 16's measurable-event information constraint before regret
calibration.  It instantiates Bretagnolle--Huber on the exact majority event
and rewrites the full history KL using the compiled one-arm specialization of
Lemma 15.1. -/
theorem bretagnolleHuberScale_expectedPulls_mul_armKL_le_majorityErrors
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (changedArm : Fin K) (lastRound : Nat)
    (hsame : forall arm, arm ≠ changedArm ->
      armLaw arm = referenceArmLaw arm) :
    bretagnolleHuberScale
        (canonicalRealizedExpectedPullCountThrough
            algorithm armLaw lastRound changedArm *
          InformationTheory.klDiv
            (armLaw changedArm) (referenceArmLaw changedArm)) <=
      (canonicalBanditHistoryMeasure algorithm armLaw lastRound).real
          (oneArmMajorityPullEvent (Reward := Reward)
            changedArm lastRound) +
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound).real
          (oneArmMajorityPullEvent (Reward := Reward)
            changedArm lastRound)ᶜ := by
  have htesting := bretagnolleHuber
    (P := canonicalBanditHistoryMeasure algorithm armLaw lastRound)
    (Q := canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound)
    (measurableSet_oneArmMajorityPullEvent
      (Reward := Reward) changedArm lastRound)
  change bretagnolleHuberScale
      (InformationTheory.klDiv
        (canonicalBanditHistoryMeasure algorithm armLaw lastRound)
        (canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound)) <=
    _ at htesting
  rw [banditHistoryRelativeEntropy_eq_expectedPulls_mul_of_only_arm_changed
    algorithm armLaw referenceArmLaw changedArm lastRound hsame] at htesting
  exact htesting

/-- Finite-information evaluation of the testing scale used when Chapter 16
passes from extended-real KL to the real logarithmic inequality. -/
theorem bretagnolleHuberScale_mul_eq_exp
    {expectedPull armInformation : ENNReal}
    (hpull : expectedPull ≠ ∞) (hinformation : armInformation ≠ ∞) :
    bretagnolleHuberScale (expectedPull * armInformation) =
      (1 / 2 : Real) * Real.exp
        (-(expectedPull.toReal * armInformation.toReal)) := by
  have hproduct : expectedPull * armInformation ≠ ∞ :=
    ENNReal.mul_ne_top hpull hinformation
  simp [bretagnolleHuberScale, hproduct, ENNReal.toReal_mul]

/-- Deterministic assembly of the two majority-event regret charges with the
Bretagnolle--Huber testing error. -/
theorem exp_testing_bound_of_majority_regret_bounds
    (expectedPull information gap changedMargin horizon
      originalError changedError originalRegret changedRegret : Real)
    (hgap : 0 < gap) (hmargin : 0 < changedMargin)
    (hhorizon : 0 < horizon)
    (horiginalError : 0 <= originalError)
    (hchangedError : 0 <= changedError)
    (htesting :
      (1 / 2 : Real) * Real.exp (-(expectedPull * information)) <=
        originalError + changedError)
    (horiginalRegret :
      horizon * gap / 2 * originalError <= originalRegret)
    (hchangedRegret :
      horizon * changedMargin / 2 * changedError <= changedRegret) :
    horizon * min gap changedMargin / 4 *
        Real.exp (-(expectedPull * information)) <=
      originalRegret + changedRegret := by
  have hmin : 0 < min gap changedMargin := lt_min hgap hmargin
  have hscale : 0 <= horizon * min gap changedMargin / 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left htesting hscale
  have hminGap : min gap changedMargin <= gap := min_le_left _ _
  have hminMargin : min gap changedMargin <= changedMargin := min_le_right _ _
  have horiginalScaled :
      horizon * min gap changedMargin / 2 * originalError <=
        originalRegret := by
    refine le_trans ?_ horiginalRegret
    gcongr
  have hchangedScaled :
      horizon * min gap changedMargin / 2 * changedError <=
        changedRegret := by
    refine le_trans ?_ hchangedRegret
    gcongr
  nlinarith

/-- The exact logarithmic rearrangement used in Lemma 16.3.  This theorem is
only the scalar consumer of the testing inequality; the bandit theorem must
still produce `htesting` from the common-policy history law, the majority
event, and the two expected pseudo-regrets. -/
theorem expectedPullCount_ge_log_regret_of_exp_testing_bound
    (expectedPull information gap changedMargin horizon regretSum : Real)
    (hinformation : 0 < information)
    (hgap : 0 < gap) (hmargin : 0 < changedMargin)
    (hhorizon : 0 < horizon)
    (htesting :
      horizon * min gap changedMargin / 4 *
          Real.exp (-(expectedPull * information)) <= regretSum) :
    (Real.log (min gap changedMargin / 4) + Real.log horizon -
        Real.log regretSum) / information <= expectedPull := by
  have hmin : 0 < min gap changedMargin := lt_min hgap hmargin
  have hfactor : 0 < horizon * min gap changedMargin / 4 := by positivity
  have hleft : 0 <
      horizon * min gap changedMargin / 4 *
        Real.exp (-(expectedPull * information)) := mul_pos hfactor (Real.exp_pos _)
  have hlog := Real.log_le_log hleft htesting
  have hfactorEq :
      horizon * min gap changedMargin / 4 =
        horizon * (min gap changedMargin / 4) := by ring
  rw [hfactorEq,
    Real.log_mul
      (mul_ne_zero hhorizon.ne'
        (div_ne_zero hmin.ne' (by norm_num : (4 : Real) ≠ 0)))
      (Real.exp_ne_zero _),
    Real.log_mul hhorizon.ne'
      (div_ne_zero hmin.ne' (by norm_num : (4 : Real) ≠ 0)),
    Real.log_exp] at hlog
  apply (div_le_iff₀ hinformation).2
  nlinarith

/-- Chapter 16's finite-time change-of-measure calculation with the actual
canonical gap pseudo-regrets produced above.  This closes the common-policy,
one-arm-KL, majority-event, exact `1/4`, and logarithmic assembly route for
explicit nonnegative gap vectors.  It is intentionally not named as source
Lemma 16.3: a later environment layer must still prove that these vectors are
the mean gaps of finite-mean arm laws and discharge the finite-positive-KL
branch from that source contract. -/
theorem expectedPullCount_ge_log_gapPseudoRegret_of_only_arm_changed
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (originalGap referenceGap : Fin K -> Real)
    (horiginalGap : forall arm, 0 <= originalGap arm)
    (hreferenceGap : forall arm, 0 <= referenceGap arm)
    (changedArm : Fin K) (changedMargin : Real)
    (hchangedGap : 0 < originalGap changedArm)
    (hmargin : 0 < changedMargin)
    (hother : forall arm, arm ≠ changedArm ->
      changedMargin <= referenceGap arm)
    (lastRound : Nat)
    (hsame : forall arm, arm ≠ changedArm ->
      armLaw arm = referenceArmLaw arm)
    (hinformation_ne_top :
      InformationTheory.klDiv
        (armLaw changedArm) (referenceArmLaw changedArm) ≠ ∞)
    (hinformation_pos : 0 <
      (InformationTheory.klDiv
        (armLaw changedArm) (referenceArmLaw changedArm)).toReal) :
    (Real.log (min (originalGap changedArm) changedMargin / 4) +
          Real.log ((lastRound + 1 : Nat) : Real) -
          Real.log
            (canonicalGapExpectedPseudoRegretReal
                algorithm armLaw originalGap lastRound +
              canonicalGapExpectedPseudoRegretReal
                algorithm referenceArmLaw referenceGap lastRound)) /
        (InformationTheory.klDiv
          (armLaw changedArm) (referenceArmLaw changedArm)).toReal <=
      (canonicalRealizedExpectedPullCountThrough
        algorithm armLaw lastRound changedArm).toReal := by
  let expectedPull := canonicalRealizedExpectedPullCountThrough
    algorithm armLaw lastRound changedArm
  let information := InformationTheory.klDiv
    (armLaw changedArm) (referenceArmLaw changedArm)
  let horizon : Real := (lastRound + 1 : Nat)
  let originalError :=
    (canonicalBanditHistoryMeasure algorithm armLaw lastRound).real
      (oneArmMajorityPullEvent (Reward := Reward) changedArm lastRound)
  let referenceError :=
    (canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound).real
      (oneArmMajorityPullEvent (Reward := Reward) changedArm lastRound)ᶜ
  let originalRegret := canonicalGapExpectedPseudoRegretReal
    algorithm armLaw originalGap lastRound
  let referenceRegret := canonicalGapExpectedPseudoRegretReal
    algorithm referenceArmLaw referenceGap lastRound
  have hpull : expectedPull ≠ ∞ := by
    exact canonicalRealizedExpectedPullCountThrough_ne_top
      algorithm armLaw lastRound changedArm
  have htesting :=
    bretagnolleHuberScale_expectedPulls_mul_armKL_le_majorityErrors
      algorithm armLaw referenceArmLaw changedArm lastRound hsame
  have htestingReal :
      (1 / 2 : Real) * Real.exp
          (-(expectedPull.toReal * information.toReal)) <=
        originalError + referenceError := by
    change bretagnolleHuberScale (expectedPull * information) <=
      originalError + referenceError at htesting
    have hinformation : information ≠ ∞ := hinformation_ne_top
    rw [bretagnolleHuberScale_mul_eq_exp hpull hinformation] at htesting
    exact htesting
  have horiginal :
      horizon * originalGap changedArm / 2 * originalError <=
        originalRegret := by
    exact oneArmMajority_probability_charge_le_expectedPseudoRegret
      algorithm armLaw originalGap horiginalGap changedArm hchangedGap lastRound
  have hreference :
      horizon * changedMargin / 2 * referenceError <=
        referenceRegret := by
    exact oneArmMajority_compl_probability_charge_le_expectedPseudoRegret
      algorithm referenceArmLaw referenceGap hreferenceGap changedArm
        changedMargin hmargin hother lastRound
  have hassembled := exp_testing_bound_of_majority_regret_bounds
    expectedPull.toReal information.toReal (originalGap changedArm)
      changedMargin horizon originalError referenceError
      originalRegret referenceRegret hchangedGap hmargin
      (by dsimp [horizon]; positivity) measureReal_nonneg measureReal_nonneg
      htestingReal horiginal hreference
  exact expectedPullCount_ge_log_regret_of_exp_testing_bound
    expectedPull.toReal information.toReal (originalGap changedArm)
      changedMargin horizon (originalRegret + referenceRegret)
      hinformation_pos hchangedGap hmargin
      (by dsimp [horizon]; positivity) hassembled

/-- The two regrets in the one-arm testing construction cannot both vanish
when arm KL is finite and both source gaps are positive. -/
theorem gapPseudoRegret_add_pos_of_only_arm_changed
    {K : Nat} {Reward : Type*}
    [MeasurableSpace Reward] [MeasurableSpace.CountablyGenerated Reward]
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Reward)
    (armLaw referenceArmLaw : Kernel (Fin K) Reward)
    [IsMarkovKernel armLaw] [IsMarkovKernel referenceArmLaw]
    (originalGap referenceGap : Fin K -> Real)
    (horiginalGap : forall arm, 0 <= originalGap arm)
    (hreferenceGap : forall arm, 0 <= referenceGap arm)
    (changedArm : Fin K) (changedMargin : Real)
    (hchangedGap : 0 < originalGap changedArm)
    (hmargin : 0 < changedMargin)
    (hother : forall arm, arm ≠ changedArm ->
      changedMargin <= referenceGap arm)
    (lastRound : Nat)
    (hsame : forall arm, arm ≠ changedArm ->
      armLaw arm = referenceArmLaw arm)
    (hinformation_ne_top :
      InformationTheory.klDiv
        (armLaw changedArm) (referenceArmLaw changedArm) ≠ ∞) :
    0 < canonicalGapExpectedPseudoRegretReal
          algorithm armLaw originalGap lastRound +
        canonicalGapExpectedPseudoRegretReal
          algorithm referenceArmLaw referenceGap lastRound := by
  let expectedPull := canonicalRealizedExpectedPullCountThrough
    algorithm armLaw lastRound changedArm
  let information := InformationTheory.klDiv
    (armLaw changedArm) (referenceArmLaw changedArm)
  let horizon : Real := (lastRound + 1 : Nat)
  let originalError :=
    (canonicalBanditHistoryMeasure algorithm armLaw lastRound).real
      (oneArmMajorityPullEvent (Reward := Reward) changedArm lastRound)
  let referenceError :=
    (canonicalBanditHistoryMeasure algorithm referenceArmLaw lastRound).real
      (oneArmMajorityPullEvent (Reward := Reward) changedArm lastRound)ᶜ
  let originalRegret := canonicalGapExpectedPseudoRegretReal
    algorithm armLaw originalGap lastRound
  let referenceRegret := canonicalGapExpectedPseudoRegretReal
    algorithm referenceArmLaw referenceGap lastRound
  have hpull : expectedPull ≠ ∞ :=
    canonicalRealizedExpectedPullCountThrough_ne_top
      algorithm armLaw lastRound changedArm
  have htesting :=
    bretagnolleHuberScale_expectedPulls_mul_armKL_le_majorityErrors
      algorithm armLaw referenceArmLaw changedArm lastRound hsame
  have htestingReal :
      (1 / 2 : Real) * Real.exp
          (-(expectedPull.toReal * information.toReal)) <=
        originalError + referenceError := by
    change bretagnolleHuberScale (expectedPull * information) <=
      originalError + referenceError at htesting
    rw [bretagnolleHuberScale_mul_eq_exp hpull hinformation_ne_top] at htesting
    exact htesting
  have horiginal :
      horizon * originalGap changedArm / 2 * originalError <=
        originalRegret :=
    oneArmMajority_probability_charge_le_expectedPseudoRegret
      algorithm armLaw originalGap horiginalGap changedArm hchangedGap lastRound
  have hreference :
      horizon * changedMargin / 2 * referenceError <=
        referenceRegret :=
    oneArmMajority_compl_probability_charge_le_expectedPseudoRegret
      algorithm referenceArmLaw referenceGap hreferenceGap changedArm
        changedMargin hmargin hother lastRound
  have hassembled := exp_testing_bound_of_majority_regret_bounds
    expectedPull.toReal information.toReal (originalGap changedArm)
      changedMargin horizon originalError referenceError
      originalRegret referenceRegret hchangedGap hmargin
      (by dsimp [horizon]; positivity) measureReal_nonneg measureReal_nonneg
      htestingReal horiginal hreference
  have hleft : 0 < horizon * min (originalGap changedArm) changedMargin / 4 *
      Real.exp (-(expectedPull.toReal * information.toReal)) := by
    have hmin : 0 < min (originalGap changedArm) changedMargin :=
      lt_min hchangedGap hmargin
    dsimp [horizon]
    positivity
  exact lt_of_lt_of_le hleft hassembled

/-- **Lattimore--Szepesvári, Lemma 16.3.**  This is the exact source
one-arm change-of-measure inequality for finite-mean product environments.
The denominator is presented through `ENNReal.toReal`; when arm KL is
infinite this evaluates the source convention `x / ∞ = 0`.  The zero-KL
case is impossible here because the changed arm has different certified
finite means. -/
theorem expectedPullCount_ge_log_regret_changeOfMeasure
    {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (original reference : FiniteMeanBanditEnvironment K)
    (changedArm : Fin K)
    (hsuboptimal :
      original.mean changedArm < original.mean original.bestArm)
    (hunique : forall arm, arm ≠ changedArm ->
      reference.mean arm < reference.mean changedArm)
    (hsame : forall arm, arm ≠ changedArm ->
      original.armLaw arm = reference.armLaw arm)
    (lastRound : Nat) :
    (Real.log
          (min
              (oneArmMeanIncrease original reference changedArm -
                original.gap changedArm)
              (original.gap changedArm) / 4) +
          Real.log ((lastRound + 1 : Nat) : Real) -
          Real.log
            (canonicalGapExpectedPseudoRegretReal
                algorithm original.armLaw original.gap lastRound +
              canonicalGapExpectedPseudoRegretReal
                algorithm reference.armLaw reference.gap lastRound)) /
        (InformationTheory.klDiv
          (original.armLaw changedArm)
          (reference.armLaw changedArm)).toReal <=
      (canonicalRealizedExpectedPullCountThrough
        algorithm original.armLaw lastRound changedArm).toReal := by
  have hcontract := oneArmMeanChange_produces_gap_contract
    original reference changedArm hsuboptimal hunique hsame
  rcases hcontract with ⟨hgap, hmargin, hother⟩
  let information := InformationTheory.klDiv
    (original.armLaw changedArm) (reference.armLaw changedArm)
  have hinformation_ne_zero : information ≠ 0 := by
    intro hzero
    have hlaw : original.armLaw changedArm = reference.armLaw changedArm :=
      InformationTheory.klDiv_eq_zero_iff.mp hzero
    have hmean := FiniteMeanBanditEnvironment.mean_eq_of_armLaw_eq
      original reference changedArm hlaw
    dsimp [oneArmChangedMargin] at hmargin
    linarith
  by_cases hinformation_top : information = ∞
  · simp [information, hinformation_top]
  · have hinformation_pos : 0 < information.toReal :=
      ENNReal.toReal_pos hinformation_ne_zero hinformation_top
    have hfinite :=
      expectedPullCount_ge_log_gapPseudoRegret_of_only_arm_changed
        algorithm original.armLaw reference.armLaw
        original.gap reference.gap original.gap_nonneg
        reference.gap_nonneg changedArm
        (oneArmChangedMargin original reference changedArm)
        hgap hmargin hother lastRound hsame hinformation_top
        hinformation_pos
    rw [← oneArmMeanIncrease_sub_gap_eq_changedMargin] at hfinite
    simpa [min_comm] using hfinite

/-- Expected regret after exactly `n` pulls, including the empty horizon. -/
def finiteMeanExpectedRegret {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : FiniteMeanBanditEnvironment K) : Nat → Real
  | 0 => 0
  | n + 1 => canonicalGapExpectedPseudoRegretReal
      algorithm environment.armLaw environment.gap n

/-- Expected pull count after exactly `n` pulls, including the empty horizon. -/
def finiteMeanExpectedPullCount {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : FiniteMeanBanditEnvironment K) (arm : Fin K) : Nat → Real
  | 0 => 0
  | n + 1 => (canonicalRealizedExpectedPullCountThrough
      algorithm environment.armLaw n arm).toReal

theorem finiteMeanExpectedPullCount_nonneg {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : FiniteMeanBanditEnvironment K) (arm : Fin K) (n : Nat) :
    0 ≤ finiteMeanExpectedPullCount algorithm environment arm n := by
  cases n <;> simp [finiteMeanExpectedPullCount]

/-- Source regret decomposition with the exact number-of-pulls horizon. -/
theorem finiteMeanExpectedRegret_eq_sum {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : FiniteMeanBanditEnvironment K) (n : Nat) :
    finiteMeanExpectedRegret algorithm environment n =
      ∑ arm, environment.gap arm * finiteMeanExpectedPullCount algorithm environment arm n := by
  cases n with
  | zero => simp [finiteMeanExpectedRegret, finiteMeanExpectedPullCount]
  | succ n =>
    exact canonicalGapExpectedPseudoRegretReal_eq_sum_expectedPulls
      algorithm environment.armLaw environment.gap environment.gap_nonneg n

/-- Extended-real normalization of the source regret decomposition. -/
theorem finiteMeanNormalizedRegret_eq_sum {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : FiniteMeanBanditEnvironment K) (n : Nat) (hn : 1 < n) :
    ENNReal.ofReal (finiteMeanExpectedRegret algorithm environment n / Real.log n) =
      ∑ arm, ENNReal.ofReal (environment.gap arm) * ENNReal.ofReal
        (finiteMeanExpectedPullCount algorithm environment arm n / Real.log n) := by
  have hlog : 0 < Real.log (n : Real) := Real.log_pos (by exact_mod_cast hn)
  rw [finiteMeanExpectedRegret_eq_sum, Finset.sum_div,
    ENNReal.ofReal_sum_of_nonneg (by
      intro arm _
      exact div_nonneg (mul_nonneg (environment.gap_nonneg arm)
        (finiteMeanExpectedPullCount_nonneg algorithm environment arm n)) hlog.le)]
  apply Finset.sum_congr rfl
  intro arm _
  rw [mul_div_assoc, ENNReal.ofReal_mul (environment.gap_nonneg arm)]

/-- Theorem 16.2's per-alternative information constraint for finite KL.
Consistency is imposed on the actual regret sequences of the two
environments, and the conclusion uses the original-law pull count. -/
theorem consistentRegret_liminf_expectedPull_div_log_ge_of_alternative
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (original reference : FiniteMeanBanditEnvironment K) (changedArm : Fin K)
    (hsuboptimal : original.mean changedArm < original.mean original.bestArm)
    (hunique : ∀ arm, arm ≠ changedArm → reference.mean arm < reference.mean changedArm)
    (hsame : ∀ arm, arm ≠ changedArm → original.armLaw arm = reference.armLaw arm)
    (hfirst : IsConsistentRegret (finiteMeanExpectedRegret algorithm original))
    (hsecond : IsConsistentRegret (finiteMeanExpectedRegret algorithm reference))
    (hfinite : InformationTheory.klDiv (original.armLaw changedArm)
      (reference.armLaw changedArm) ≠ ∞) :
    ENNReal.ofReal (1 / (InformationTheory.klDiv (original.armLaw changedArm)
      (reference.armLaw changedArm)).toReal) ≤
      liminf (fun n : Nat => ENNReal.ofReal
        (finiteMeanExpectedPullCount algorithm original changedArm n / Real.log n)) atTop := by
  obtain ⟨hgap, hmargin, hother⟩ := oneArmMeanChange_produces_gap_contract
    original reference changedArm hsuboptimal hunique hsame
  have hnonzero : InformationTheory.klDiv (original.armLaw changedArm)
      (reference.armLaw changedArm) ≠ 0 := by
    intro hzero
    have heq := original.mean_eq_of_armLaw_eq reference changedArm
      (InformationTheory.klDiv_eq_zero_iff.mp hzero)
    dsimp [oneArmChangedMargin] at hmargin
    linarith
  apply hfirst.liminf_pull_div_log_ge hsecond (c := Real.log
    (min (oneArmMeanIncrease original reference changedArm - original.gap changedArm)
      (original.gap changedArm) / 4))
  · filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
    cases n with
    | zero => omega
    | succ n =>
      exact gapPseudoRegret_add_pos_of_only_arm_changed
        algorithm original.armLaw reference.armLaw original.gap reference.gap
        original.gap_nonneg reference.gap_nonneg changedArm
        (oneArmChangedMargin original reference changedArm)
        hgap hmargin hother n hsame hfinite
  · exact ENNReal.toReal_pos hnonzero hfinite
  · filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
    cases n with
    | zero => omega
    | succ n =>
      exact expectedPullCount_ge_log_regret_changeOfMeasure
        algorithm original reference changedArm hsuboptimal hunique hsame n

/-- The exact per-arm information constraint supporting Theorem 16.2.
The inverse infimum remains extended-real: zero infimum forces infinite
liminf, while an empty or all-infinite alternative class contributes zero. -/
theorem consistentPolicy_liminf_expectedPull_div_log_ge_inv_dInf
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (componentClass : Fin K → Set (Measure Real))
    (hfinite : ∀ arm P, P ∈ componentClass arm →
      IsProbabilityMeasure P ∧ Integrable id P)
    (hconsistent : IsConsistentPolicyOver
      {environment : FiniteMeanBanditEnvironment K |
        environment.InUnstructuredClass componentClass}
      finiteMeanExpectedRegret algorithm)
    (original : FiniteMeanBanditEnvironment K)
    (hclass : original.InUnstructuredClass componentClass)
    (changedArm : Fin K)
    (hsuboptimal : original.mean changedArm < original.mean original.bestArm) :
    (divergenceInfimum (original.armLaw changedArm)
      (original.mean original.bestArm) (componentClass changedArm)
      (fun P => ∫ x, x ∂P))⁻¹ ≤
      liminf (fun n : Nat => ENNReal.ofReal
        (finiteMeanExpectedPullCount algorithm original changedArm n / Real.log n)) atTop := by
  unfold divergenceInfimum
  rw [ENNReal.inv_sInf]
  apply iSup_le
  intro cost
  apply iSup_le
  rintro ⟨alternative, halt, hbetter, rfl⟩
  obtain ⟨hprob, hi⟩ := hfinite changedArm alternative halt
  letI : IsProbabilityMeasure alternative := hprob
  by_cases htop : relativeEntropy (original.armLaw changedArm) alternative = ∞
  · simp [htop]
  have hzero : relativeEntropy (original.armLaw changedArm) alternative ≠ 0 := by
    intro hz
    have heq : original.armLaw changedArm = alternative :=
      InformationTheory.klDiv_eq_zero_iff.mp hz
    have hm := original.mean_eq_integral changedArm
    rw [heq] at hm
    linarith [original.isBest changedArm]
  let reference := original.withImprovedArm changedArm alternative hi hbetter
  have hreference : reference.InUnstructuredClass componentClass :=
    original.withImprovedArm_mem componentClass hclass changedArm alternative hi hbetter halt
  have hresult := consistentRegret_liminf_expectedPull_div_log_ge_of_alternative
    algorithm original reference changedArm hsuboptimal
    (fun arm hne => original.withImprovedArm_unique changedArm alternative hi hbetter arm hne)
    (by intro arm hne; simp [reference, hne])
    (hconsistent original hclass) (hconsistent reference hreference)
    (by simpa [reference] using htop)
  have hpos := ENNReal.toReal_pos hzero htop
  simpa only [reference, FiniteMeanBanditEnvironment.withImprovedArm_law,
    ite_true, one_div, ENNReal.ofReal_inv_of_pos hpos,
    ENNReal.ofReal_toReal htop] using hresult

/-- **Lattimore--Szepesvári, Theorem 16.2.** The unstructured finite-mean
product-class regret lower bound, including zero and infinite information
costs. All quotients and the liminf are extended-real. -/
theorem consistentPolicy_liminf_expectedRegret_div_log_ge
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (componentClass : Fin K → Set (Measure Real))
    (hfinite : ∀ arm P, P ∈ componentClass arm →
      IsProbabilityMeasure P ∧ Integrable id P)
    (hconsistent : IsConsistentPolicyOver
      {environment : FiniteMeanBanditEnvironment K |
        environment.InUnstructuredClass componentClass}
      finiteMeanExpectedRegret algorithm)
    (original : FiniteMeanBanditEnvironment K)
    (hclass : original.InUnstructuredClass componentClass) :
    (∑ arm : Fin K with 0 < original.gap arm,
      ENNReal.ofReal (original.gap arm) /
        divergenceInfimum (original.armLaw arm) (original.mean original.bestArm)
          (componentClass arm) (fun P => ∫ x, x ∂P)) ≤
      liminf (fun n : Nat => ENNReal.ofReal
        (finiteMeanExpectedRegret algorithm original n / Real.log n)) atTop := by
  classical
  let term := fun (n : Nat) (arm : Fin K) => ENNReal.ofReal (original.gap arm) *
    ENNReal.ofReal (finiteMeanExpectedPullCount algorithm original arm n / Real.log n)
  have hterm (arm : Fin K) (hgap : 0 < original.gap arm) :
      ENNReal.ofReal (original.gap arm) /
        divergenceInfimum (original.armLaw arm) (original.mean original.bestArm)
          (componentClass arm) (fun P => ∫ x, x ∂P) ≤
      liminf (fun n => term n arm) atTop := by
    have hpull := consistentPolicy_liminf_expectedPull_div_log_ge_inv_dInf
      algorithm componentClass hfinite hconsistent original hclass arm
      (sub_pos.mp hgap)
    have hmul := ENNReal.le_liminf_mul
      (u := fun _ : Nat => ENNReal.ofReal (original.gap arm))
      (v := fun n : Nat => ENNReal.ofReal
        (finiteMeanExpectedPullCount algorithm original arm n / Real.log n))
      (f := atTop)
    calc
      _ ≤ ENNReal.ofReal (original.gap arm) *
          liminf (fun n : Nat => ENNReal.ofReal
            (finiteMeanExpectedPullCount algorithm original arm n / Real.log n)) atTop :=
        mul_le_mul_left' hpull _
      _ ≤ _ := by simpa only [liminf_const, Pi.mul_apply] using hmul
  have hfatou : (∑ arm, liminf (fun n => term n arm) atTop) ≤
      liminf (fun n => ∑ arm, term n arm) atTop := by
    simpa only [lintegral_count, tsum_fintype] using
      (lintegral_liminf_le (μ := Measure.count) (f := term)
        (fun n => measurable_of_countable _))
  calc
    _ ≤ ∑ arm : Fin K with 0 < original.gap arm,
        liminf (fun n => term n arm) atTop := by
      apply Finset.sum_le_sum
      intro arm harm
      exact hterm arm (Finset.mem_filter.mp harm).2
    _ ≤ ∑ arm : Fin K, liminf (fun n => term n arm) atTop :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intros; exact zero_le _)
    _ ≤ liminf (fun n => ∑ arm, term n arm) atTop := hfatou
    _ = _ := by
      apply Filter.liminf_congr
      filter_upwards [eventually_gt_atTop (1 : Nat)] with n hn
      exact (finiteMeanNormalizedRegret_eq_sum algorithm original n hn).symm

/-- Per-arm finite-time Gaussian consequence used in Theorem 16.4, before
summing and taking positive parts.  Both regret bounds are retained
explicitly so the published `2 C n^p` denominator is visible. -/
theorem gaussianExpectedPullCount_ge_finiteTimeInstanceDependent
    {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : UnitVarianceGaussianBanditEnvironment K)
    (changedArm : Fin K) (epsilon C p : Real)
    (hgap : 0 < environment.gap changedArm)
    (hepsilon : 0 < epsilon) (hepsilon_one : epsilon <= 1)
    (_hC : 0 < C)
    (lastRound : Nat)
    (hbase :
      unitVarianceGaussianExpectedPseudoRegret
          algorithm environment lastRound <=
        C * (((lastRound + 1 : Nat) : Real) ^ p))
    (hchanged :
      unitVarianceGaussianExpectedPseudoRegret algorithm
          (chapter16GaussianChangedEnvironment environment changedArm epsilon
            hgap hepsilon) lastRound <=
        C * (((lastRound + 1 : Nat) : Real) ^ p)) :
    (Real.log (epsilon * environment.gap changedArm / 4) +
          Real.log ((lastRound + 1 : Nat) : Real) -
          Real.log
            (2 * C * (((lastRound + 1 : Nat) : Real) ^ p))) /
        (((1 + epsilon) * environment.gap changedArm) ^ 2 / 2) <=
      (canonicalRealizedExpectedPullCountThrough algorithm
        (unitGaussianKernel environment.mean) lastRound changedArm).toReal := by
  let changed := chapter16GaussianChangedEnvironment
    environment changedArm epsilon hgap hepsilon
  have hsuboptimal :
      environment.toFiniteMean.mean changedArm <
        environment.toFiniteMean.mean environment.toFiniteMean.bestArm := by
    exact sub_pos.mp hgap
  have hunique : forall arm, arm ≠ changedArm ->
      changed.toFiniteMean.mean arm < changed.toFiniteMean.mean changedArm := by
    exact chapter16GaussianChangedEnvironment_uniqueBest
      environment changedArm epsilon hgap hepsilon
  have hsame : forall arm, arm ≠ changedArm ->
      environment.toFiniteMean.armLaw arm = changed.toFiniteMean.armLaw arm := by
    exact chapter16GaussianChangedEnvironment_sameArmLaw
      environment changedArm epsilon hgap hepsilon
  have hinformation_ne_top :
      InformationTheory.klDiv
        (environment.toFiniteMean.armLaw changedArm)
        (changed.toFiniteMean.armLaw changedArm) ≠ ∞ := by
    rw [chapter16GaussianChangedEnvironment_armKL]
    exact ENNReal.ofReal_ne_top
  have hsumpos :
      0 < unitVarianceGaussianExpectedPseudoRegret
            algorithm environment lastRound +
          unitVarianceGaussianExpectedPseudoRegret
            algorithm changed lastRound := by
    simpa [unitVarianceGaussianExpectedPseudoRegret, changed] using
      gapPseudoRegret_add_pos_of_only_arm_changed
        algorithm environment.toFiniteMean.armLaw changed.toFiniteMean.armLaw
        environment.toFiniteMean.gap changed.toFiniteMean.gap
        environment.toFiniteMean.gap_nonneg changed.toFiniteMean.gap_nonneg
        changedArm
        (oneArmChangedMargin environment.toFiniteMean changed.toFiniteMean
          changedArm)
        hgap
        (by
          dsimp [changed]
          rw [chapter16GaussianChangedEnvironment_changedMargin]
          exact mul_pos hepsilon hgap)
        (oneArmMeanChange_produces_gap_contract
          environment.toFiniteMean changed.toFiniteMean changedArm
          hsuboptimal hunique hsame).2.2
        lastRound hsame hinformation_ne_top
  have hsumUpper :
      unitVarianceGaussianExpectedPseudoRegret
            algorithm environment lastRound +
          unitVarianceGaussianExpectedPseudoRegret
            algorithm changed lastRound <=
        2 * C * (((lastRound + 1 : Nat) : Real) ^ p) := by
    dsimp [changed] at hchanged ⊢
    nlinarith
  have hlogUpper := Real.log_le_log hsumpos hsumUpper
  have hsource := expectedPullCount_ge_log_regret_changeOfMeasure
    algorithm environment.toFiniteMean changed.toFiniteMean changedArm
      hsuboptimal hunique hsame lastRound
  have hmargin :
      oneArmMeanIncrease environment.toFiniteMean changed.toFiniteMean changedArm -
          environment.toFiniteMean.gap changedArm =
        epsilon * environment.gap changedArm := by
    rw [oneArmMeanIncrease_sub_gap_eq_changedMargin]
    simpa [changed] using chapter16GaussianChangedEnvironment_changedMargin
      environment changedArm epsilon hgap hepsilon
  have hmin : min (epsilon * environment.gap changedArm)
      (environment.gap changedArm) =
        epsilon * environment.gap changedArm := by
    exact min_eq_left (by nlinarith)
  have hdenom : 0 < ((1 + epsilon) * environment.gap changedArm) ^ 2 / 2 := by
    positivity
  have hnum :
      Real.log (epsilon * environment.gap changedArm / 4) +
            Real.log ((lastRound + 1 : Nat) : Real) -
            Real.log (2 * C * (((lastRound + 1 : Nat) : Real) ^ p)) <=
        Real.log (epsilon * environment.gap changedArm / 4) +
            Real.log ((lastRound + 1 : Nat) : Real) -
            Real.log
              (unitVarianceGaussianExpectedPseudoRegret
                  algorithm environment lastRound +
                unitVarianceGaussianExpectedPseudoRegret
                  algorithm changed lastRound) := by
    linarith
  apply le_trans ((div_le_div_iff_of_pos_right hdenom).2 hnum)
  simp only [UnitVarianceGaussianBanditEnvironment.toFiniteMean_gap] at hmargin
  simp only [UnitVarianceGaussianBanditEnvironment.toFiniteMean_gap] at hsource
  rw [hmargin, hmin,
    chapter16GaussianChangedEnvironment_armKL_toReal] at hsource
  simpa [unitVarianceGaussianExpectedPseudoRegret, changed] using hsource

/-- Exact logarithmic normalization in the displayed bound (16.5). -/
theorem chapter16Gaussian_finiteTime_log_identity
    (epsilon gap C p horizon : Real)
    (hepsilon : 0 < epsilon) (hgap : 0 < gap)
    (hC : 0 < C) (hhorizon : 0 < horizon) :
    Real.log (epsilon * gap / 4) + Real.log horizon -
        Real.log (2 * C * horizon ^ p) =
      (1 - p) * Real.log horizon +
        Real.log (epsilon * gap / (8 * C)) := by
  have hfour : (4 : Real) ≠ 0 := by norm_num
  have height : (8 : Real) ≠ 0 := by norm_num
  have htwo : (2 : Real) ≠ 0 := by norm_num
  have hpow : horizon ^ p ≠ 0 := (Real.rpow_pos_of_pos hhorizon p).ne'
  have hlogEight : Real.log (8 : Real) =
      Real.log (2 : Real) + Real.log (4 : Real) := by
    rw [show (8 : Real) = 2 * 4 by norm_num, Real.log_mul htwo hfour]
  rw [Real.log_div (mul_ne_zero hepsilon.ne' hgap.ne') hfour,
    Real.log_mul hepsilon.ne' hgap.ne',
    Real.log_mul (mul_ne_zero htwo hC.ne') hpow,
    Real.log_mul htwo hC.ne',
    Real.log_rpow hhorizon,
    Real.log_div (mul_ne_zero hepsilon.ne' hgap.ne')
      (mul_ne_zero height hC.ne'),
    Real.log_mul hepsilon.ne' hgap.ne',
    Real.log_mul height hC.ne', hlogEight]
  ring

/-- **Lattimore--Szepesvári, Theorem 16.4.**  Finite-time
instance-dependent lower bound for arbitrary unit-variance Gaussian means.
`lastRound + 1` is the source horizon `n`; the supplied set `N` is therefore
stated on positive horizon lengths. -/
theorem gaussianExpectedRegret_ge_finiteTimeInstanceDependent
    {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : UnitVarianceGaussianBanditEnvironment K)
    (horizons : Set Nat) (hhorizons : horizons.Nonempty)
    (C p : Real) (hC : 0 < C) (_hp : p ∈ Set.Ioo (0 : Real) 1)
    (hregret : forall (lastRound : Nat), lastRound + 1 ∈ horizons ->
      forall candidate : UnitVarianceGaussianBanditEnvironment K,
        InChapter16GaussianLocalClass environment candidate ->
        unitVarianceGaussianExpectedPseudoRegret
            algorithm candidate lastRound <=
          C * (((lastRound + 1 : Nat) : Real) ^ p))
    (epsilon : Real) (hepsilon : epsilon ∈ Set.Ioc (0 : Real) 1)
    (lastRound : Nat) (hhorizon : lastRound + 1 ∈ horizons) :
    unitVarianceGaussianExpectedPseudoRegret algorithm environment lastRound >=
      2 / (1 + epsilon) ^ 2 *
        ∑ arm ∈ Finset.univ.filter (fun arm : Fin K =>
            0 < environment.gap arm),
          max
            (((1 - p) * Real.log ((lastRound + 1 : Nat) : Real) +
                Real.log (epsilon * environment.gap arm / (8 * C))) /
              environment.gap arm)
            0 := by
  classical
  have _ := hhorizons
  have hepsilon_pos : 0 < epsilon := hepsilon.1
  have hepsilon_one : epsilon <= 1 := hepsilon.2
  have hbase := hregret lastRound hhorizon environment
    (inChapter16GaussianLocalClass_self environment)
  have hdecomp :
      unitVarianceGaussianExpectedPseudoRegret algorithm environment lastRound =
        ∑ arm : Fin K, environment.gap arm *
          (canonicalRealizedExpectedPullCountThrough algorithm
            (unitGaussianKernel environment.mean) lastRound arm).toReal := by
    exact canonicalGapExpectedPseudoRegretReal_eq_sum_expectedPulls
      algorithm (unitGaussianKernel environment.mean) environment.gap
      environment.gap_nonneg lastRound
  rw [hdecomp]
  calc
    2 / (1 + epsilon) ^ 2 *
          ∑ arm ∈ Finset.univ.filter (fun arm : Fin K =>
              0 < environment.gap arm),
            max
              (((1 - p) * Real.log ((lastRound + 1 : Nat) : Real) +
                  Real.log (epsilon * environment.gap arm / (8 * C))) /
                environment.gap arm)
              0 =
        ∑ arm ∈ Finset.univ.filter (fun arm : Fin K =>
            0 < environment.gap arm),
          2 / (1 + epsilon) ^ 2 *
            max
              (((1 - p) * Real.log ((lastRound + 1 : Nat) : Real) +
                  Real.log (epsilon * environment.gap arm / (8 * C))) /
                environment.gap arm)
              0 := by rw [Finset.mul_sum]
    _ <= ∑ arm ∈ Finset.univ.filter (fun arm : Fin K =>
            0 < environment.gap arm),
          environment.gap arm *
            (canonicalRealizedExpectedPullCountThrough algorithm
              (unitGaussianKernel environment.mean) lastRound arm).toReal := by
      apply Finset.sum_le_sum
      intro arm harm
      have hgap : 0 < environment.gap arm :=
        (Finset.mem_filter.mp harm).2
      let changed := chapter16GaussianChangedEnvironment
        environment arm epsilon hgap hepsilon_pos
      have hchanged := hregret lastRound hhorizon changed
        (by
          dsimp [changed]
          exact inChapter16GaussianLocalClass_changed environment arm epsilon
            hgap hepsilon_pos hepsilon_one)
      have hpull := gaussianExpectedPullCount_ge_finiteTimeInstanceDependent
        algorithm environment arm epsilon C p hgap hepsilon_pos
          hepsilon_one hC lastRound hbase (by simpa [changed] using hchanged)
      have hlog := chapter16Gaussian_finiteTime_log_identity
        epsilon (environment.gap arm) C p
        ((lastRound + 1 : Nat) : Real) hepsilon_pos hgap hC (by positivity)
      rw [hlog] at hpull
      have hscaled := mul_le_mul_of_nonneg_left hpull hgap.le
      have hfactor : 0 <= 2 / (1 + epsilon) ^ 2 := by positivity
      have halgebra :
          environment.gap arm *
              (((1 - p) * Real.log ((lastRound + 1 : Nat) : Real) +
                  Real.log (epsilon * environment.gap arm / (8 * C))) /
                (((1 + epsilon) * environment.gap arm) ^ 2 / 2)) =
            2 / (1 + epsilon) ^ 2 *
              (((1 - p) * Real.log ((lastRound + 1 : Nat) : Real) +
                  Real.log (epsilon * environment.gap arm / (8 * C))) /
                environment.gap arm) := by
        field_simp [hgap.ne', (by nlinarith [hepsilon_pos] : 1 + epsilon ≠ 0)]
      rw [halgebra] at hscaled
      rw [mul_max_of_nonneg _ _ hfactor, mul_zero]
      exact max_le hscaled (mul_nonneg hgap.le ENNReal.toReal_nonneg)
    _ <= ∑ arm : Fin K, environment.gap arm *
          (canonicalRealizedExpectedPullCountThrough algorithm
            (unitGaussianKernel environment.mean) lastRound arm).toReal := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro arm _huniv hnot
        exact mul_nonneg (environment.gap_nonneg arm) ENNReal.toReal_nonneg

end

end LowerBounds
end BanditRLProof
