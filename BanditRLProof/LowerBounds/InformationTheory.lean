import BanditRLProof.Algorithms.KLUCBBernoulli
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Information-theoretic lower-bound foundations

This file formalizes the measure-KL and event-testing surface used in Part IV,
Chapter 14 of Lattimore--Szepesvári, *Bandit Algorithms*.  Measure-level
relative entropy is Mathlib's extended-real `InformationTheory.klDiv`.
The project-local work below keeps absolute continuity, integrability, KL
direction, Bernoulli endpoints, and the infinite-divergence branch explicit.
-/

namespace BanditRLProof
namespace LowerBounds

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- Chapter 14 relative entropy, with value `∞` on support mismatch or a
non-integrable log-likelihood ratio. -/
abbrev relativeEntropy {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) : ENNReal :=
  InformationTheory.klDiv P Q

/-- The finite regular branch of the Radon--Nikodym representation.  The mass
correction vanishes when `P` and `Q` are probability measures. -/
theorem relativeEntropy_of_absolutelyContinuous_of_integrable
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    (hPQ : P ≪ Q) (hInt : Integrable (llr P Q) P) :
    relativeEntropy P Q =
      ENNReal.ofReal
        (∫ x, llr P Q x ∂P + Q.real univ - P.real univ) :=
  InformationTheory.klDiv_of_ac_of_integrable hPQ hInt

/-- Probability-measure specialization of Theorem 14.1: the finite relative
entropy is exactly the expected log likelihood ratio. -/
theorem relativeEntropy_of_probability_absolutelyContinuous_of_integrable
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hInt : Integrable (llr P Q) P) :
    relativeEntropy P Q = ENNReal.ofReal (∫ x, llr P Q x ∂P) := by
  rw [relativeEntropy_of_absolutelyContinuous_of_integrable P Q hPQ hInt,
    probReal_univ, probReal_univ]
  ring_nf

/-- The singular branch of Theorem 14.1. -/
theorem relativeEntropy_eq_top_of_not_absolutelyContinuous
    {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    (hPQ : ¬ P ≪ Q) :
    relativeEntropy P Q = ∞ :=
  InformationTheory.klDiv_of_not_ac hPQ

/-- Exact finiteness contract for the Mathlib representation of Chapter 14
relative entropy. -/
theorem relativeEntropy_ne_top_iff
    {α : Type*} [MeasurableSpace α] {P Q : Measure α} :
    relativeEntropy P Q ≠ ∞ ↔ P ≪ Q ∧ Integrable (llr P Q) P :=
  InformationTheory.klDiv_ne_top_iff

/-- The Bernoulli relative entropy from Eq. (14.4), reusing the project's exact
support and endpoint convention. -/
abbrev bernoulliRelativeEntropy (p q : Real) : ENNReal :=
  KLUCB.bernoulliKL p q

/-- Restricting both laws to a measurable event preserves the original
Radon--Nikodym derivative almost everywhere on that event. -/
theorem rnDeriv_restrict_restrict
    {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    [SigmaFinite P] [SigmaFinite Q]
    (hPQ : P ≪ Q) {A : Set α} (hA : MeasurableSet A) :
    (P.restrict A).rnDeriv (Q.restrict A) =ᵐ[Q.restrict A]
      P.rnDeriv Q := by
  have hDensity :
      (Q.restrict A).withDensity (P.rnDeriv Q) = P.restrict A := by
    rw [← restrict_withDensity hA,
      Measure.withDensity_rnDeriv_eq P Q hPQ]
  have hRN := Measure.rnDeriv_withDensity (Q.restrict A)
    (Measure.measurable_rnDeriv P Q)
  simpa only [hDensity] using hRN

/-- Relative entropy splits exactly across an event and its complement.  This
is the two-cell partition identity used by the event data-processing proof. -/
theorem relativeEntropy_restrict_add_compl
    {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P ≪ Q) {A : Set α} (hA : MeasurableSet A) :
    relativeEntropy P Q =
      relativeEntropy (P.restrict A) (Q.restrict A) +
        relativeEntropy (P.restrict Aᶜ) (Q.restrict Aᶜ) := by
  change InformationTheory.klDiv P Q =
    InformationTheory.klDiv (P.restrict A) (Q.restrict A) +
      InformationTheory.klDiv (P.restrict Aᶜ) (Q.restrict Aᶜ)
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hPQ,
    InformationTheory.klDiv_eq_lintegral_klFun_of_ac (hPQ.restrict A),
    InformationTheory.klDiv_eq_lintegral_klFun_of_ac (hPQ.restrict Aᶜ)]
  have hRN := rnDeriv_restrict_restrict hPQ hA
  have hRNc := rnDeriv_restrict_restrict hPQ hA.compl
  let f : α → ENNReal := fun x =>
    ENNReal.ofReal (InformationTheory.klFun (P.rnDeriv Q x).toReal)
  change (∫⁻ x, f x ∂Q) =
    (∫⁻ x, ENNReal.ofReal
      (InformationTheory.klFun
        ((P.restrict A).rnDeriv (Q.restrict A) x).toReal) ∂Q.restrict A) +
    (∫⁻ x, ENNReal.ofReal
      (InformationTheory.klFun
        ((P.restrict Aᶜ).rnDeriv (Q.restrict Aᶜ) x).toReal) ∂Q.restrict Aᶜ)
  calc
    (∫⁻ x, f x ∂Q) =
        ∫⁻ x, f x ∂(Q.restrict A + Q.restrict Aᶜ) := by
      rw [Measure.restrict_add_restrict_compl hA]
    _ = (∫⁻ x, f x ∂Q.restrict A) +
          ∫⁻ x, f x ∂Q.restrict Aᶜ := by
      rw [lintegral_add_measure]
    _ = _ := by
      congr 1
      · apply lintegral_congr_ae
        filter_upwards [hRN] with x hx
        simp [f, hx]
      · apply lintegral_congr_ae
        filter_upwards [hRNc] with x hx
        simp [f, hx]

/-- Event data processing in the finite, non-singular Bernoulli branch.  This
is the quantitative core of Exercise 14.10 specialized to the sigma-algebra
generated by one event. -/
theorem bernoulliKLCore_event_le
    {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set α} (hA : MeasurableSet A)
    (hKL : relativeEntropy P Q ≠ ∞)
    (hQ0 : 0 < Q.real A) (hQ1 : Q.real A < 1) :
    KLUCB.bernoulliKLCore (P.real A) (Q.real A) ≤
      (relativeEntropy P Q).toReal := by
  have hReg := relativeEntropy_ne_top_iff.mp hKL
  have hSplit := relativeEntropy_restrict_add_compl hReg.1 hA
  have hLeftFinite :
      relativeEntropy (P.restrict A) (Q.restrict A) ≠ ∞ := by
    intro hTop
    apply hKL
    rw [hSplit, hTop, top_add]
  have hRightFinite :
      relativeEntropy (P.restrict Aᶜ) (Q.restrict Aᶜ) ≠ ∞ := by
    intro hTop
    apply hKL
    rw [hSplit, hTop, add_top]
  have hLeftReg := relativeEntropy_ne_top_iff.mp hLeftFinite
  have hRightReg := relativeEntropy_ne_top_iff.mp hRightFinite
  have hLeft := InformationTheory.mul_klFun_le_toReal_klDiv
    hLeftReg.1 hLeftReg.2
  have hRight := InformationTheory.mul_klFun_le_toReal_klDiv
    hRightReg.1 hRightReg.2
  have hLeft' :
      Q.real A * InformationTheory.klFun (P.real A / Q.real A) ≤
        (relativeEntropy (P.restrict A) (Q.restrict A)).toReal := by
    simpa only [measureReal_restrict_apply_univ] using hLeft
  have hRight' :
      Q.real Aᶜ * InformationTheory.klFun (P.real Aᶜ / Q.real Aᶜ) ≤
        (relativeEntropy (P.restrict Aᶜ) (Q.restrict Aᶜ)).toReal := by
    simpa only [measureReal_restrict_apply_univ] using hRight
  have hPCompl : P.real Aᶜ = 1 - P.real A := by
    linarith [probReal_add_probReal_compl (μ := P) hA]
  have hQCompl : Q.real Aᶜ = 1 - Q.real A := by
    linarith [probReal_add_probReal_compl (μ := Q) hA]
  rw [KLUCB.bernoulliKLCore_eq_klFun
    (ne_of_gt hQ0) (ne_of_lt hQ1)]
  calc
    Q.real A * InformationTheory.klFun (P.real A / Q.real A) +
        (1 - Q.real A) *
          InformationTheory.klFun ((1 - P.real A) / (1 - Q.real A)) =
      Q.real A * InformationTheory.klFun (P.real A / Q.real A) +
        Q.real Aᶜ * InformationTheory.klFun (P.real Aᶜ / Q.real Aᶜ) := by
          rw [hPCompl, hQCompl]
    _ ≤ (relativeEntropy (P.restrict A) (Q.restrict A)).toReal +
          (relativeEntropy (P.restrict Aᶜ) (Q.restrict Aᶜ)).toReal :=
      add_le_add hLeft' hRight'
    _ = (relativeEntropy P Q).toReal := by
      rw [hSplit, ENNReal.toReal_add hLeftFinite hRightFinite]

private theorem mul_sqrt_div_eq_sqrt_mul
    {a b : Real} (ha : 0 < a) (hb : 0 ≤ b) :
    a * Real.sqrt (b / a) = Real.sqrt (a * b) := by
  calc
    a * Real.sqrt (b / a) = a * (Real.sqrt b / Real.sqrt a) := by
      rw [Real.sqrt_div hb]
    _ = Real.sqrt a * Real.sqrt b := by
      calc
        a * (Real.sqrt b / Real.sqrt a) =
            (Real.sqrt a * Real.sqrt a) *
              (Real.sqrt b / Real.sqrt a) := by
          rw [Real.mul_self_sqrt ha.le]
        _ = Real.sqrt a * Real.sqrt b := by
          field_simp [Real.sqrt_ne_zero'.mpr ha]
    _ = Real.sqrt (a * b) := (Real.sqrt_mul ha.le b).symm

/-- The binary likelihood affinity dominates `exp(-d/2)`.  This is the
two-atom Jensen step in the source proof of Theorem 14.2. -/
theorem exp_neg_half_bernoulliKLCore_le_affinity
    {p q : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    Real.exp (-(KLUCB.bernoulliKLCore p q) / 2) ≤
      Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q)) := by
  let x : Real := Real.sqrt (q / p)
  let y : Real := Real.sqrt ((1 - q) / (1 - p))
  have hxPos : 0 < x := by
    dsimp [x]
    exact Real.sqrt_pos.2 (div_pos hq0 hp0)
  have hyPos : 0 < y := by
    dsimp [y]
    exact Real.sqrt_pos.2 (div_pos (sub_pos.mpr hq1) (sub_pos.mpr hp1))
  have hJensen :
      p * Real.log x + (1 - p) * Real.log y ≤
        Real.log (p * x + (1 - p) * y) := by
    simpa only [smul_eq_mul] using
      (strictConcaveOn_log_Ioi).concaveOn.2 hxPos hyPos hp0.le
        (sub_nonneg.mpr hp1.le) (by ring : p + (1 - p) = 1)
  have hLogX :
      Real.log x = -(Real.log (p / q)) / 2 := by
    dsimp [x]
    rw [Real.log_sqrt (div_nonneg hq0.le hp0.le),
      Real.log_div (ne_of_gt hq0) (ne_of_gt hp0),
      Real.log_div (ne_of_gt hp0) (ne_of_gt hq0)]
    ring
  have hLogY :
      Real.log y = -(Real.log ((1 - p) / (1 - q))) / 2 := by
    dsimp [y]
    have hpComp : 0 < 1 - p := sub_pos.mpr hp1
    have hqComp : 0 < 1 - q := sub_pos.mpr hq1
    rw [Real.log_sqrt (div_nonneg hqComp.le hpComp.le),
      Real.log_div (ne_of_gt hqComp) (ne_of_gt hpComp),
      Real.log_div (ne_of_gt hpComp) (ne_of_gt hqComp)]
    ring
  have hWeightedAffinity :
      p * x + (1 - p) * y =
        Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q)) := by
    dsimp [x, y]
    rw [mul_sqrt_div_eq_sqrt_mul hp0 hq0.le,
      mul_sqrt_div_eq_sqrt_mul (sub_pos.mpr hp1)
        (sub_nonneg.mpr hq1.le)]
  have hLog :
      -(KLUCB.bernoulliKLCore p q) / 2 ≤
        Real.log (Real.sqrt (p * q) +
          Real.sqrt ((1 - p) * (1 - q))) := by
    calc
      -(KLUCB.bernoulliKLCore p q) / 2 =
          p * Real.log x + (1 - p) * Real.log y := by
        rw [hLogX, hLogY]
        unfold KLUCB.bernoulliKLCore
        ring
      _ ≤ Real.log (p * x + (1 - p) * y) := hJensen
      _ = _ := by rw [hWeightedAffinity]
  have hAffinityPos :
      0 < Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q)) := by
    have : 0 < Real.sqrt (p * q) := Real.sqrt_pos.2 (mul_pos hp0 hq0)
    positivity
  calc
    Real.exp (-(KLUCB.bernoulliKLCore p q) / 2) ≤
        Real.exp (Real.log (Real.sqrt (p * q) +
          Real.sqrt ((1 - p) * (1 - q)))) :=
      Real.exp_le_exp.mpr hLog
    _ = _ := Real.exp_log hAffinityPos

/-- The two-atom Le Cam overlap inequality in the orientation needed for an
event `A`: the affinity squared, divided by two, is bounded by
`p + (1 - q)`. -/
theorem half_binaryAffinity_sq_le_eventError
    {p q : Real} (hp : KLUCB.IsBernoulliParameter p)
    (hq : KLUCB.IsBernoulliParameter q) :
    (1 / 2 : Real) *
        (Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q))) ^ 2 ≤
      p + (1 - q) := by
  have hpqNonneg : 0 ≤ p * q := mul_nonneg hp.1 hq.1
  have hpqLe : p * q ≤ p := by nlinarith [hp.1, hq.2]
  have hCompNonneg : 0 ≤ (1 - p) * (1 - q) :=
    mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hq.2)
  have hCompLe : (1 - p) * (1 - q) ≤ 1 - q := by
    nlinarith [hp.1, hp.2, hq.2]
  have hAffinityLe :
      Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q)) ≤
        Real.sqrt p + Real.sqrt (1 - q) :=
    add_le_add (Real.sqrt_le_sqrt hpqLe) (Real.sqrt_le_sqrt hCompLe)
  have hAffinityNonneg :
      0 ≤ Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q)) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hSimpleNonneg : 0 ≤ Real.sqrt p + Real.sqrt (1 - q) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hSquareLe :
      (Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q))) ^ 2 ≤
        (Real.sqrt p + Real.sqrt (1 - q)) ^ 2 := by
    nlinarith
  have hSqrtP := Real.sq_sqrt hp.1
  have hSqrtComp := Real.sq_sqrt (sub_nonneg.mpr hq.2)
  have hCross := sq_nonneg (Real.sqrt p - Real.sqrt (1 - q))
  have hSimpleSquare :
      (Real.sqrt p + Real.sqrt (1 - q)) ^ 2 ≤
        2 * (p + (1 - q)) := by
    nlinarith
  nlinarith

/-- Bretagnolle--Huber for the finite analytic Bernoulli KL expression. -/
theorem binaryBretagnolleHuberCore
    {p q : Real} (hp : KLUCB.IsBernoulliParameter p)
    (hq0 : 0 < q) (hq1 : q < 1) :
    (1 / 2 : Real) * Real.exp (-KLUCB.bernoulliKLCore p q) ≤
      p + (1 - q) := by
  by_cases hp0 : p = 0
  · subst p
    have hCore :
        KLUCB.bernoulliKLCore 0 q = -Real.log (1 - q) := by
      simp [KLUCB.bernoulliKLCore]
    rw [hCore, neg_neg, Real.exp_log (sub_pos.mpr hq1)]
    nlinarith [hq1.le]
  by_cases hp1 : p = 1
  · subst p
    have hCore : KLUCB.bernoulliKLCore 1 q = -Real.log q := by
      simp [KLUCB.bernoulliKLCore]
    rw [hCore, neg_neg, Real.exp_log hq0]
    nlinarith [hq1.le]
  have hp0' : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hp0)
  have hp1' : p < 1 := lt_of_le_of_ne hp.2 hp1
  have hAffinity := exp_neg_half_bernoulliKLCore_le_affinity
    hp0' hp1' hq0 hq1
  have hExpNonneg :
      0 ≤ Real.exp (-(KLUCB.bernoulliKLCore p q) / 2) :=
    (Real.exp_pos _).le
  have hAffinityNonneg :
      0 ≤ Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q)) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hSquare :
      (Real.exp (-(KLUCB.bernoulliKLCore p q) / 2)) ^ 2 ≤
        (Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q))) ^ 2 := by
    nlinarith
  have hExpSquare :
      (Real.exp (-(KLUCB.bernoulliKLCore p q) / 2)) ^ 2 =
        Real.exp (-KLUCB.bernoulliKLCore p q) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hLeCam := half_binaryAffinity_sq_le_eventError hp
    (show KLUCB.IsBernoulliParameter q from ⟨hq0.le, hq1.le⟩)
  rw [hExpSquare] at hSquare
  nlinarith

/-- The source convention `exp(-∞)=0`, exposed as a real-valued testing
scale so Theorem 14.2 remains unconditional. -/
noncomputable def bretagnolleHuberScale (d : ENNReal) : Real :=
  if d = ∞ then 0 else (1 / 2 : Real) * Real.exp (-d.toReal)

theorem bretagnolleHuberScale_nonneg (d : ENNReal) :
    0 ≤ bretagnolleHuberScale d := by
  by_cases h : d = ∞
  · simp [bretagnolleHuberScale, h]
  · simp only [bretagnolleHuberScale, h, ↓reduceIte]
    positivity

/-- Exact two-atom Bretagnolle--Huber inequality, including singular
Bernoulli endpoints through the extended-real testing scale. -/
theorem binaryBretagnolleHuber
    {p q : Real} (hp : KLUCB.IsBernoulliParameter p)
    (hq : KLUCB.IsBernoulliParameter q) :
    bretagnolleHuberScale (bernoulliRelativeEntropy p q) ≤
      p + (1 - q) := by
  change bretagnolleHuberScale (KLUCB.bernoulliKL p q) ≤
    p + (1 - q)
  by_cases hq0 : q = 0
  · subst q
    by_cases hp0 : p = 0
    · subst p
      norm_num [bretagnolleHuberScale, KLUCB.bernoulliKL_zero_zero]
    · rw [KLUCB.bernoulliKL_eq_top_right_zero hp hp0]
      simp [bretagnolleHuberScale]
      linarith [hp.1]
  by_cases hq1 : q = 1
  · subst q
    by_cases hp1 : p = 1
    · subst p
      norm_num [bretagnolleHuberScale, KLUCB.bernoulliKL_one_one]
    · rw [KLUCB.bernoulliKL_eq_top_right_one hp hp1]
      simp [bretagnolleHuberScale]
      exact hp.1
  have hq0' : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hq0)
  have hq1' : q < 1 := lt_of_le_of_ne hq.2 hq1
  have hCoreNonneg := KLUCB.bernoulliKLCore_nonneg hp hq0' hq1'
  rw [KLUCB.bernoulliKL_eq_of_interior hp hq0' hq1']
  simp only [bretagnolleHuberScale, ENNReal.ofReal_ne_top,
    ↓reduceIte, ENNReal.toReal_ofReal hCoreNonneg]
  exact binaryBretagnolleHuberCore hp hq0' hq1'

/-- Event-level binary data processing: observing only membership in `A`
cannot increase the relative entropy. -/
theorem bernoulliRelativeEntropy_event_le
    {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set α} (hA : MeasurableSet A) :
    bernoulliRelativeEntropy (P.real A) (Q.real A) ≤
      relativeEntropy P Q := by
  change KLUCB.bernoulliKL (P.real A) (Q.real A) ≤
    InformationTheory.klDiv P Q
  by_cases hKL : InformationTheory.klDiv P Q = ∞
  · simp [hKL]
  have hReg := relativeEntropy_ne_top_iff.mp hKL
  have hP : KLUCB.IsBernoulliParameter (P.real A) :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hQ : KLUCB.IsBernoulliParameter (Q.real A) :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  by_cases hQ0 : Q.real A = 0
  · have hQZero : Q A = 0 := (measureReal_eq_zero_iff).mp hQ0
    have hPZero : P A = 0 := hReg.1 hQZero
    have hP0 : P.real A = 0 := (measureReal_eq_zero_iff).mpr hPZero
    rw [hQ0, hP0, KLUCB.bernoulliKL_zero_zero]
    exact bot_le
  by_cases hQ1 : Q.real A = 1
  · have hQComplReal : Q.real Aᶜ = 0 := by
      linarith [probReal_add_probReal_compl (μ := Q) hA]
    have hQCompl : Q Aᶜ = 0 :=
      (measureReal_eq_zero_iff).mp hQComplReal
    have hPCompl : P Aᶜ = 0 := hReg.1 hQCompl
    have hPComplReal : P.real Aᶜ = 0 :=
      (measureReal_eq_zero_iff).mpr hPCompl
    have hP1 : P.real A = 1 := by
      linarith [probReal_add_probReal_compl (μ := P) hA]
    rw [hQ1, hP1, KLUCB.bernoulliKL_one_one]
    exact bot_le
  have hQ0' : 0 < Q.real A := lt_of_le_of_ne hQ.1 (Ne.symm hQ0)
  have hQ1' : Q.real A < 1 := lt_of_le_of_ne hQ.2 hQ1
  have hCore := bernoulliKLCore_event_le hA hKL hQ0' hQ1'
  calc
    KLUCB.bernoulliKL (P.real A) (Q.real A) =
        ENNReal.ofReal
          (KLUCB.bernoulliKLCore (P.real A) (Q.real A)) :=
      KLUCB.bernoulliKL_eq_of_interior hP hQ0' hQ1'
    _ ≤ ENNReal.ofReal (InformationTheory.klDiv P Q).toReal :=
      ENNReal.ofReal_le_ofReal hCore
    _ = InformationTheory.klDiv P Q :=
      ENNReal.ofReal_toReal hKL

/-- The Bretagnolle--Huber testing scale is antitone in its information
argument. -/
theorem bretagnolleHuberScale_antitone {d D : ENNReal} (h : d ≤ D) :
    bretagnolleHuberScale D ≤ bretagnolleHuberScale d := by
  by_cases hD : D = ∞
  · simpa [bretagnolleHuberScale, hD] using
      bretagnolleHuberScale_nonneg d
  have hd : d ≠ ∞ := by
    intro hd
    subst d
    exact hD (top_unique h)
  simp only [bretagnolleHuberScale, hD, hd, ↓reduceIte]
  have hReal := ENNReal.toReal_mono hD h
  have hExp : Real.exp (-D.toReal) ≤ Real.exp (-d.toReal) :=
    Real.exp_le_exp.mpr (neg_le_neg hReal)
  nlinarith

/-- **Bretagnolle--Huber inequality** (Lattimore--Szepesvári, Theorem 14.2).
For any measurable event, the two testing errors are bounded below in the
source KL direction `D(P,Q)`.  The infinite-divergence case is included by
`bretagnolleHuberScale`. -/
theorem bretagnolleHuber
    {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set α} (hA : MeasurableSet A) :
    bretagnolleHuberScale (relativeEntropy P Q) ≤
      P.real A + Q.real Aᶜ := by
  have hP : KLUCB.IsBernoulliParameter (P.real A) :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hQ : KLUCB.IsBernoulliParameter (Q.real A) :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hDPI := bernoulliRelativeEntropy_event_le (P := P) (Q := Q) hA
  have hScale := bretagnolleHuberScale_antitone hDPI
  have hBinary := binaryBretagnolleHuber hP hQ
  have hQCompl : Q.real Aᶜ = 1 - Q.real A := by
    linarith [probReal_add_probReal_compl (μ := Q) hA]
  calc
    bretagnolleHuberScale (relativeEntropy P Q) ≤
        bretagnolleHuberScale
          (bernoulliRelativeEntropy (P.real A) (Q.real A)) := hScale
    _ ≤ P.real A + (1 - Q.real A) := hBinary
    _ = P.real A + Q.real Aᶜ := by rw [hQCompl]

end

end LowerBounds
end BanditRLProof
