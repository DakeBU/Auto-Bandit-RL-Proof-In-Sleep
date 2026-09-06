import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Bernoulli relative entropy and KL confidence indices

This file owns the project-local binary relative entropy used by KL-UCB.  The
codomain is `ENNReal`: singular Bernoulli comparisons are genuinely `top`, not
the accidental finite value obtained from Mathlib's totalized `Real.log 0`.
-/

namespace BanditRLProof
namespace KLUCB

open Set

noncomputable section

/-- The closed unit interval predicate used by every KL-UCB parameter. -/
def IsBernoulliParameter (p : Real) : Prop := p ∈ Set.Icc (0 : Real) 1

local instance (p : Real) : Decidable (IsBernoulliParameter p) :=
  Classical.propDecidable _

local instance : DecidableEq Real := Classical.decEq _

/-- The finite analytic Bernoulli relative-entropy expression.  It is used
only when the second parameter is strictly between zero and one. -/
noncomputable def bernoulliKLCore (p q : Real) : Real :=
  p * Real.log (p / q) +
    (1 - p) * Real.log ((1 - p) / (1 - q))

/-- Bernoulli relative entropy with exact support/endpoint conventions.

* parameters outside `[0,1]` have value `top`;
* `d(0,0)=d(1,1)=0`;
* `d(p,0)=top` for `p>0` and `d(p,1)=top` for `p<1`;
* otherwise the ordinary finite logarithmic expression is used.
-/
noncomputable def bernoulliKL (p q : Real) : ENNReal :=
  if hp : IsBernoulliParameter p then
    if hq : IsBernoulliParameter q then
      if hq0 : q = 0 then
        if hp0 : p = 0 then 0 else ⊤
      else if hq1 : q = 1 then
        if hp1 : p = 1 then 0 else ⊤
      else
        ENNReal.ofReal (bernoulliKLCore p q)
    else ⊤
  else ⊤

theorem bernoulliKL_nonneg (p q : Real) :
    0 <= bernoulliKL p q := bot_le

@[simp]
theorem bernoulliKL_eq_top_of_not_left
    {p q : Real} (hp : ¬ IsBernoulliParameter p) :
    bernoulliKL p q = ⊤ := by
  simp [bernoulliKL, hp]

@[simp]
theorem bernoulliKL_eq_top_of_not_right
    {p q : Real} (hq : ¬ IsBernoulliParameter q) :
    bernoulliKL p q = ⊤ := by
  by_cases hp : IsBernoulliParameter p
  · simp [bernoulliKL, hp, hq]
  · simp [bernoulliKL, hp]

@[simp]
theorem bernoulliKL_zero_zero : bernoulliKL 0 0 = 0 := by
  simp [bernoulliKL, IsBernoulliParameter]

@[simp]
theorem bernoulliKL_one_one : bernoulliKL 1 1 = 0 := by
  simp [bernoulliKL, IsBernoulliParameter]

@[simp]
theorem bernoulliKL_right_zero
    {p : Real} (hp : IsBernoulliParameter p) :
    bernoulliKL p 0 = if p = 0 then 0 else ⊤ := by
  have hzero : IsBernoulliParameter (0 : Real) := ⟨le_rfl, zero_le_one⟩
  simp [bernoulliKL, hp, hzero]

@[simp]
theorem bernoulliKL_right_one
    {p : Real} (hp : IsBernoulliParameter p) :
    bernoulliKL p 1 = if p = 1 then 0 else ⊤ := by
  have hone : IsBernoulliParameter (1 : Real) := ⟨zero_le_one, le_rfl⟩
  simp [bernoulliKL, hp, hone]

theorem bernoulliKL_eq_top_right_zero
    {p : Real} (hp : IsBernoulliParameter p) (hp0 : p ≠ 0) :
    bernoulliKL p 0 = ⊤ := by
  simp [bernoulliKL_right_zero hp, hp0]

theorem bernoulliKL_eq_top_right_one
    {p : Real} (hp : IsBernoulliParameter p) (hp1 : p ≠ 1) :
    bernoulliKL p 1 = ⊤ := by
  simp [bernoulliKL_right_one hp, hp1]

theorem bernoulliKL_zero_left_of_interior
    {q : Real} (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliKL 0 q =
      ENNReal.ofReal (Real.log (1 / (1 - q))) := by
  have hq : IsBernoulliParameter q := ⟨hq0.le, hq1.le⟩
  have hzero : IsBernoulliParameter (0 : Real) := ⟨le_rfl, zero_le_one⟩
  have hq0ne : q ≠ 0 := ne_of_gt hq0
  have hq1ne : q ≠ 1 := ne_of_lt hq1
  rw [show Real.log (1 / (1 - q)) = -Real.log (1 - q) by
    rw [one_div, Real.log_inv]]
  simp [bernoulliKL, hzero, hq, hq0ne, hq1ne, bernoulliKLCore]

theorem bernoulliKL_one_left_of_interior
    {q : Real} (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliKL 1 q =
      ENNReal.ofReal (Real.log (1 / q)) := by
  have hq : IsBernoulliParameter q := ⟨hq0.le, hq1.le⟩
  have hone : IsBernoulliParameter (1 : Real) := ⟨zero_le_one, le_rfl⟩
  have hq0ne : q ≠ 0 := ne_of_gt hq0
  have hq1ne : q ≠ 1 := ne_of_lt hq1
  rw [show Real.log (1 / q) = -Real.log q by rw [one_div, Real.log_inv]]
  simp [bernoulliKL, hone, hq, hq0ne, hq1ne, bernoulliKLCore]

/-- The finite Bernoulli expression vanishes on the diagonal away from the
singular endpoints. -/
theorem bernoulliKLCore_self
    {p : Real} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    bernoulliKLCore p p = 0 := by
  simp [bernoulliKLCore, hp0, hp1]

/-- The analytic binary KL expression is the two-atom `klFun` integral. -/
theorem bernoulliKLCore_eq_klFun
    {p q : Real} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    bernoulliKLCore p q =
      q * InformationTheory.klFun (p / q) +
        (1 - q) * InformationTheory.klFun ((1 - p) / (1 - q)) := by
  rw [InformationTheory.klFun_apply, InformationTheory.klFun_apply]
  unfold bernoulliKLCore
  have h1q : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  field_simp
  ring

/-- Nontrivial nonnegativity of the finite logarithmic expression.  This is
stronger than the order-theoretic nonnegativity of its `ENNReal` wrapper. -/
theorem bernoulliKLCore_nonneg
    {p q : Real} (hp : IsBernoulliParameter p)
    (hq0 : 0 < q) (hq1 : q < 1) :
    0 <= bernoulliKLCore p q := by
  rw [bernoulliKLCore_eq_klFun (ne_of_gt hq0) (ne_of_lt hq1)]
  have hpq : 0 <= p / q := div_nonneg hp.1 hq0.le
  have hcomp : 0 <= (1 - p) / (1 - q) := by
    exact div_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hq1.le)
  exact add_nonneg
    (mul_nonneg hq0.le (InformationTheory.klFun_nonneg hpq))
    (mul_nonneg (sub_nonneg.mpr hq1.le)
      (InformationTheory.klFun_nonneg hcomp))

/-- Interior parameters expose the finite analytic expression without
truncation: its real nonnegativity has already been proved. -/
theorem bernoulliKL_eq_of_interior
    {p q : Real} (hp : IsBernoulliParameter p)
    (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliKL p q = ENNReal.ofReal (bernoulliKLCore p q) := by
  have hq : IsBernoulliParameter q := ⟨hq0.le, hq1.le⟩
  have hq0ne : q ≠ 0 := ne_of_gt hq0
  have hq1ne : q ≠ 1 := ne_of_lt hq1
  simp [bernoulliKL, hp, hq, hq0ne, hq1ne]

/-- Algebraically expanded finite KL, convenient for differentiation in the
second parameter. -/
noncomputable def bernoulliKLExpanded (p q : Real) : Real :=
  p * Real.log p - p * Real.log q +
    (1 - p) * Real.log (1 - p) -
      (1 - p) * Real.log (1 - q)

theorem bernoulliKLCore_eq_expanded
    {p q : Real} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    bernoulliKLCore p q = bernoulliKLExpanded p q := by
  unfold bernoulliKLCore bernoulliKLExpanded
  rw [Real.log_div hp0 hq0,
    Real.log_div (sub_ne_zero.mpr (Ne.symm hp1))
      (sub_ne_zero.mpr (Ne.symm hq1))]
  ring

theorem hasDerivAt_bernoulliKLExpanded_right
    (p q : Real) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    HasDerivAt (fun r => bernoulliKLExpanded p r)
      ((q - p) / (q * (1 - q))) q := by
  unfold bernoulliKLExpanded
  have hlogq := Real.hasDerivAt_log hq0
  have h1q : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have honeSub : HasDerivAt (fun r : Real => 1 - r) (-1) q := by
    convert (hasDerivAt_const q (1 : Real)).sub (hasDerivAt_id q) using 1 <;> ring
  have hlogOneSub := honeSub.log (sub_ne_zero.mpr (Ne.symm hq1))
  convert
    (((hasDerivAt_const q (p * Real.log p)).sub
        (hlogq.const_mul p)).add
      (hasDerivAt_const q ((1 - p) * Real.log (1 - p)))).sub
        (hlogOneSub.const_mul (1 - p)) using 1 <;>
      field_simp [hq0, h1q] <;> ring

/-- A conservative binary Pinsker inequality.  The constant `1/2` is weaker
than the sharp natural-log constant `2`, but is sufficient to invert every
KL-UCB confidence set without changing the KL score itself. -/
theorem half_sq_sub_le_bernoulliKLCore
    {p q : Real} (hp : IsBernoulliParameter p)
    (hq0 : 0 < q) (hq1 : q < 1) :
    (1 / 2 : Real) * (p - q) ^ 2 <= bernoulliKLCore p q := by
  by_cases hp0 : p = 0
  · subst p
    simp only [zero_sub, neg_sq]
    have hlog := Real.log_le_sub_one_of_pos (sub_pos.mpr hq1)
    have hqle : (1 / 2 : Real) * q ^ 2 <= q := by
      nlinarith [hq0.le, hq1.le]
    simpa [bernoulliKLCore] using hqle.trans (by linarith : q <= -Real.log (1 - q))
  by_cases hp1 : p = 1
  · subst p
    have hlog := Real.log_le_sub_one_of_pos hq0
    have hcomp : 0 <= 1 - q := sub_nonneg.mpr hq1.le
    have hcomple : 1 - q <= 1 := by linarith
    have hsq : (1 / 2 : Real) * (1 - q) ^ 2 <= 1 - q := by
      nlinarith
    simpa [bernoulliKLCore] using hsq.trans (by linarith : 1 - q <= -Real.log q)
  have hp0' : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hp0)
  have hp1' : p < 1 := lt_of_le_of_ne hp.2 hp1
  let f : Real -> Real := fun r =>
    bernoulliKLExpanded p r - (1 / 2 : Real) * (p - r) ^ 2
  have hfderiv (r : Real) (hr0 : 0 < r) (hr1 : r < 1) :
      HasDerivAt f
        ((r - p) * (1 / (r * (1 - r)) - 1)) r := by
    have hkl := hasDerivAt_bernoulliKLExpanded_right p r
      (ne_of_gt hr0) (ne_of_lt hr1)
    have hdiff : HasDerivAt (fun x : Real => p - x) (-1) r := by
      convert (hasDerivAt_const r p).sub (hasDerivAt_id r) using 1 <;> ring
    have hsq : HasDerivAt
        (fun x : Real => (1 / 2 : Real) * (p - x) ^ 2) (r - p) r := by
      convert (hdiff.pow 2).const_mul (1 / 2 : Real) using 1 <;> ring
    convert hkl.sub hsq using 1
    field_simp [ne_of_gt hr0, sub_ne_zero.mpr (Ne.symm (ne_of_lt hr1))]
  have hcoefficient (r : Real) (hr0 : 0 < r) (hr1 : r < 1) :
      0 <= 1 / (r * (1 - r)) - 1 := by
    have hprod : 0 < r * (1 - r) := mul_pos hr0 (sub_pos.mpr hr1)
    have hprod_le : r * (1 - r) <= 1 := by nlinarith [sq_nonneg r]
    have hone : (1 : Real) <= 1 / (r * (1 - r)) := by
      exact (le_div_iff₀ hprod).2 (by simpa using hprod_le)
    linarith
  have hfp : f p = 0 := by
    simp [f, bernoulliKLExpanded]
  have hresult : f p <= f q := by
    rcases le_total p q with hpq | hqp
    · let D : Set Real := Set.Icc p q
      have hinside (r : Real) (hr : r ∈ D) : 0 < r ∧ r < 1 :=
        ⟨hp0'.trans_le hr.1, hr.2.trans_lt hq1⟩
      have hcontinuous : ContinuousOn f D := by
        intro r hr
        exact (hfderiv r (hinside r hr).1 (hinside r hr).2).continuousAt.continuousWithinAt
      have hmono : MonotoneOn f D :=
        monotoneOn_of_deriv_nonneg (convex_Icc p q) hcontinuous
          (fun r hr => (hfderiv r
            (hinside r (interior_subset hr)).1
            (hinside r (interior_subset hr)).2).differentiableAt.differentiableWithinAt)
          (fun r hr => by
            rw [(hfderiv r
              (hinside r (interior_subset hr)).1
              (hinside r (interior_subset hr)).2).deriv]
            exact mul_nonneg (sub_nonneg.mpr (interior_subset hr).1)
              (hcoefficient r
                (hinside r (interior_subset hr)).1
                (hinside r (interior_subset hr)).2))
      exact hmono ⟨le_rfl, hpq⟩ ⟨hpq, le_rfl⟩ hpq
    · let D : Set Real := Set.Icc q p
      have hinside (r : Real) (hr : r ∈ D) : 0 < r ∧ r < 1 :=
        ⟨hq0.trans_le hr.1, hr.2.trans_lt hp1'⟩
      have hcontinuous : ContinuousOn f D := by
        intro r hr
        exact (hfderiv r (hinside r hr).1 (hinside r hr).2).continuousAt.continuousWithinAt
      have hanti : AntitoneOn f D :=
        antitoneOn_of_deriv_nonpos (convex_Icc q p) hcontinuous
          (fun r hr => (hfderiv r
            (hinside r (interior_subset hr)).1
            (hinside r (interior_subset hr)).2).differentiableAt.differentiableWithinAt)
          (fun r hr => by
            rw [(hfderiv r
              (hinside r (interior_subset hr)).1
              (hinside r (interior_subset hr)).2).deriv]
            exact mul_nonpos_of_nonpos_of_nonneg
              (sub_nonpos.mpr (interior_subset hr).2)
              (hcoefficient r
                (hinside r (interior_subset hr)).1
                (hinside r (interior_subset hr)).2))
      exact hanti ⟨le_rfl, hqp⟩ ⟨hqp, le_rfl⟩ hqp
  rw [hfp] at hresult
  have hcore := bernoulliKLCore_eq_expanded hp0 hp1
    (ne_of_gt hq0) (ne_of_lt hq1)
  simpa [f, hcore] using hresult

/-- On an interior reference mean, binary KL is controlled by the squared
deviation divided by the Bernoulli variance denominator.  This is the bridge
from the repository's bounded-reward empirical-mean tails to a genuine KL
confidence event. -/
theorem bernoulliKLCore_le_sq_div
    {p q : Real} (hp : IsBernoulliParameter p)
    (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliKLCore p q <= (p - q) ^ 2 / (q * (1 - q)) := by
  have hqcomp : 0 < 1 - q := sub_pos.mpr hq1
  by_cases hp0 : p = 0
  · subst p
    have hlog := Real.one_sub_inv_le_log_of_pos hqcomp
    have hcore : bernoulliKLCore 0 q = -Real.log (1 - q) := by
      simp [bernoulliKLCore]
    have hden : q * (1 - q) ≠ 0 := mul_ne_zero (ne_of_gt hq0) (ne_of_gt hqcomp)
    rw [hcore]
    calc
      -Real.log (1 - q) <= (1 - q)⁻¹ - 1 := by linarith
      _ = (0 - q) ^ 2 / (q * (1 - q)) := by
        field_simp [hden, ne_of_gt hqcomp]
        ring
  by_cases hp1 : p = 1
  · subst p
    have hlog := Real.one_sub_inv_le_log_of_pos hq0
    have hcore : bernoulliKLCore 1 q = -Real.log q := by
      simp [bernoulliKLCore]
    have hden : q * (1 - q) ≠ 0 := mul_ne_zero (ne_of_gt hq0) (ne_of_gt hqcomp)
    rw [hcore]
    calc
      -Real.log q <= q⁻¹ - 1 := by linarith
      _ = (1 - q) ^ 2 / (q * (1 - q)) := by
        field_simp [hden, ne_of_gt hq0, ne_of_gt hqcomp]
  · have hp0' : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hp0)
    have hp1' : p < 1 := lt_of_le_of_ne hp.2 hp1
    have hfirst := Real.log_le_sub_one_of_pos (div_pos hp0' hq0)
    have hsecond := Real.log_le_sub_one_of_pos
      (div_pos (sub_pos.mpr hp1') hqcomp)
    have hfirstMul :
        p * Real.log (p / q) <= p * (p / q - 1) :=
      mul_le_mul_of_nonneg_left hfirst hp.1
    have hsecondMul :
        (1 - p) * Real.log ((1 - p) / (1 - q)) <=
          (1 - p) * ((1 - p) / (1 - q) - 1) :=
      mul_le_mul_of_nonneg_left hsecond (sub_nonneg.mpr hp.2)
    unfold bernoulliKLCore
    calc
      p * Real.log (p / q) +
          (1 - p) * Real.log ((1 - p) / (1 - q)) <=
        p * (p / q - 1) +
          (1 - p) * ((1 - p) / (1 - q) - 1) :=
            add_le_add hfirstMul hsecondMul
      _ = (p - q) ^ 2 / (q * (1 - q)) := by
        field_simp [ne_of_gt hq0, ne_of_gt hqcomp]
        ring

theorem ennnreal_half_sq_sub_le_bernoulliKL
    {p q : Real} (hp : IsBernoulliParameter p)
    (hq0 : 0 < q) (hq1 : q < 1) :
    ENNReal.ofReal ((1 / 2 : Real) * (p - q) ^ 2) <= bernoulliKL p q := by
  rw [bernoulliKL_eq_of_interior hp hq0 hq1]
  exact ENNReal.ofReal_le_ofReal (half_sq_sub_le_bernoulliKLCore hp hq0 hq1)

theorem bernoulliKL_le_of_sq_le
    {p q budget : Real} (hp : IsBernoulliParameter p)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hsq : (p - q) ^ 2 / (q * (1 - q)) <= budget) :
    bernoulliKL p q <= ENNReal.ofReal budget := by
  rw [bernoulliKL_eq_of_interior hp hq0 hq1]
  exact ENNReal.ofReal_le_ofReal
    ((bernoulliKLCore_le_sq_div hp hq0 hq1).trans hsq)

@[simp]
theorem bernoulliKL_self
    {p : Real} (hp : IsBernoulliParameter p) :
    bernoulliKL p p = 0 := by
  by_cases hp0 : p = 0
  · subst p
    exact bernoulliKL_zero_zero
  by_cases hp1 : p = 1
  · subst p
    exact bernoulliKL_one_one
  simp [bernoulliKL, hp, hp0, hp1, bernoulliKLCore_self hp0 hp1]

/-- On the nonsingular right-parameter domain the finite expression is
continuous.  This is the local analytic regularity used by later inversion
leaves; endpoint singularities remain in `ENNReal`. -/
theorem continuousAt_bernoulliKLCore_right
    (p q : Real) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    ContinuousAt (fun r => bernoulliKLCore p r) q := by
  by_cases hp0 : p = 0
  · subst p
    have hq1' : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
    simp [bernoulliKLCore]
    fun_prop (disch := assumption)
  by_cases hp1 : p = 1
  · subst p
    simp [bernoulliKLCore]
    fun_prop (disch := assumption)
  · unfold bernoulliKLCore
    have hq1' : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
    have hpq : p / q ≠ 0 := div_ne_zero hp0 hq0
    have hpcq : (1 - p) / (1 - q) ≠ 0 := by
      exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hp1)) hq1'
    fun_prop (disch := assumption)

/-- KL confidence set at one empirical mean, pull count, and exploration
budget. -/
def confidenceSet (empiricalMean : Real) (count : Nat) (budget : Real) :
    Set Real :=
  {q | IsBernoulliParameter q ∧
    (count : ENNReal) * bernoulliKL empiricalMean q <=
      ENNReal.ofReal budget}

/-- The KL-UCB index is the supremum of its confidence set. -/
noncomputable def index
    (empiricalMean : Real) (count : Nat) (budget : Real) : Real :=
  sSup (confidenceSet empiricalMean count budget)

theorem confidenceSet_bddAbove
    (empiricalMean : Real) (count : Nat) (budget : Real) :
    BddAbove (confidenceSet empiricalMean count budget) := by
  refine ⟨1, ?_⟩
  intro q hq
  exact hq.1.2

theorem mem_confidenceSet_self
    {p : Real} (hp : IsBernoulliParameter p)
    (count : Nat) {budget : Real} (hbudget : 0 <= budget) :
    p ∈ confidenceSet p count budget := by
  constructor
  · exact hp
  · simp [bernoulliKL_self hp, hbudget]

/-- Real finite-KL arithmetic is sufficient to establish exact membership in
the `ENNReal` confidence set. -/
theorem mem_confidenceSet_of_natCast_mul_core_le
    {p q budget : Real} {count : Nat}
    (hp : IsBernoulliParameter p) (hq0 : 0 < q) (hq1 : q < 1)
    (hbudget : (count : Real) * bernoulliKLCore p q <= budget) :
    q ∈ confidenceSet p count budget := by
  constructor
  · exact ⟨hq0.le, hq1.le⟩
  · rw [bernoulliKL_eq_of_interior hp hq0 hq1,
      ← ENNReal.ofReal_natCast count,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg count)]
    exact ENNReal.ofReal_le_ofReal hbudget

theorem natCast_mul_half_sq_sub_le_budget_of_mem
    {p q budget : Real} {count : Nat}
    (hp : IsBernoulliParameter p) (hq0 : 0 < q) (hq1 : q < 1)
    (hbudget : 0 <= budget) (hmem : q ∈ confidenceSet p count budget) :
    (count : Real) * ((1 / 2 : Real) * (p - q) ^ 2) <= budget := by
  have hfinite := hmem.2
  rw [bernoulliKL_eq_of_interior hp hq0 hq1,
    ← ENNReal.ofReal_natCast count,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg count)] at hfinite
  have hreal : (count : Real) * bernoulliKLCore p q <= budget :=
    (ENNReal.ofReal_le_ofReal_iff hbudget).mp hfinite
  exact (mul_le_mul_of_nonneg_left
    (half_sq_sub_le_bernoulliKLCore hp hq0 hq1)
    (Nat.cast_nonneg count)).trans hreal

theorem confidenceSet_nonempty
    {p : Real} (hp : IsBernoulliParameter p)
    (count : Nat) {budget : Real} (hbudget : 0 <= budget) :
    (confidenceSet p count budget).Nonempty :=
  ⟨p, mem_confidenceSet_self hp count hbudget⟩

theorem index_le_one
    {p : Real} (hp : IsBernoulliParameter p)
    (count : Nat) {budget : Real} (hbudget : 0 <= budget) :
    index p count budget <= 1 := by
  unfold index
  exact csSup_le (confidenceSet_nonempty hp count hbudget)
    (fun _ hq => hq.1.2)

theorem index_nonneg
    {p : Real} (hp : IsBernoulliParameter p)
    (count : Nat) {budget : Real} (hbudget : 0 <= budget) :
    0 <= index p count budget := by
  have hp_le : p <= index p count budget := by
    exact le_csSup (confidenceSet_bddAbove p count budget)
      (mem_confidenceSet_self hp count hbudget)
  exact hp.1.trans hp_le

theorem index_mem_Icc
    {p : Real} (hp : IsBernoulliParameter p)
    (count : Nat) {budget : Real} (hbudget : 0 <= budget) :
    index p count budget ∈ Set.Icc (0 : Real) 1 :=
  ⟨index_nonneg hp count hbudget, index_le_one hp count hbudget⟩

/-- Zero empirical count makes every unit-interval parameter feasible.  This
is the explicit KL-UCB zero-count convention. -/
theorem mem_confidenceSet_zero_iff
    (p q budget : Real) (hbudget : 0 <= budget) :
    q ∈ confidenceSet p 0 budget ↔ IsBernoulliParameter q := by
  simp [confidenceSet, hbudget]

theorem index_zero_count
    {p : Real} (hp : IsBernoulliParameter p)
    {budget : Real} (hbudget : 0 <= budget) :
    index p 0 budget = 1 := by
  apply le_antisymm
  · exact index_le_one hp 0 hbudget
  · unfold index
    apply le_csSup (confidenceSet_bddAbove p 0 budget)
    exact (mem_confidenceSet_zero_iff p 1 budget hbudget).2
      ⟨zero_le_one, le_rfl⟩

/-- Membership of the true mean implies KL optimism. -/
theorem le_index_of_mem_confidenceSet
    {p q : Real} {count : Nat} {budget : Real}
    (hq : q ∈ confidenceSet p count budget) :
    q <= index p count budget := by
  unfold index
  exact le_csSup (confidenceSet_bddAbove p count budget) hq

/-- A strict lower level below the supremum has a genuine feasible witness.
No unproved claim that the supremum itself belongs to the set is used. -/
theorem exists_mem_confidenceSet_of_lt_index
    {p level : Real} {count : Nat} {budget : Real}
    (hp : IsBernoulliParameter p) (hbudget : 0 <= budget)
    (hlevel : level < index p count budget) :
    ∃ q ∈ confidenceSet p count budget, level < q := by
  unfold index at hlevel
  exact (lt_csSup_iff
    (confidenceSet_bddAbove p count budget)
    (confidenceSet_nonempty hp count hbudget)).1 hlevel

end
end KLUCB
end BanditRLProof
