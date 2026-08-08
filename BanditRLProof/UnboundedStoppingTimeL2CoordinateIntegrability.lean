import BanditRLProof.MeasureL2Indicator
import BanditRLProof.OFULScheduledUnboundedStoppingTimeExpectedRegretRate
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# L2 stopping fibers and unbounded stopped-value integrability

This module provides the countable-fiber transport needed when an unbounded
`WithTop Nat` stopping time has an L2 round count and the deterministic-time
coordinates have a uniform L2 bound. The argument is a measurable equality-
fiber decomposition plus Holder; it is not optional stopping.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof

universe u

/-- The squared successor-round count is the countable sum of its weighted
equality fibers. This is an equality in `ENNReal`, so no integrability
assumption is needed. -/
theorem tsum_natSuccSquare_mul_stoppingFiberMeasure_eq_lintegral_rounds_sq
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (hfinite : ∀ᵐ omega ∂mu, tau omega ≠ ⊤) :
    (∑' n : Nat,
      ((((n + 1) ^ 2 : Nat) : ENNReal) *
        mu {omega | tau omega = (n : WithTop Nat)})) =
      ∫⁻ omega,
        ENNReal.ofReal
          (((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) ∂mu := by
  let rounds : Omega -> Real := fun omega =>
    (((tau omega).untopA + 1 : Nat) : Real)
  let fiber : Nat -> Set Omega := fun n =>
    {omega | tau omega = (n : WithTop Nat)}
  let term : Nat -> Omega -> ENNReal := fun n =>
    (fiber n).indicator (fun _ => ((((n + 1) ^ 2 : Nat) : ENNReal)))
  have hfiberMeasurable (n : Nat) : MeasurableSet (fiber n) := by
    exact measurableSet_eq_fun htau measurable_const
  have htermMeasurable (n : Nat) : AEMeasurable (term n) mu := by
    exact (Measurable.indicator measurable_const
      (hfiberMeasurable n)).aemeasurable
  have htermIntegral (n : Nat) :
      ∫⁻ omega, term n omega ∂mu =
        ((((n + 1) ^ 2 : Nat) : ENNReal) * mu (fiber n)) := by
    unfold term
    rw [lintegral_indicator_const (hfiberMeasurable n)]
  have hpoint : ∀ᵐ omega ∂mu,
      (∑' n : Nat, term n omega) = ENNReal.ofReal (rounds omega ^ 2) := by
    filter_upwards [hfinite] with omega htop
    lift tau omega to Nat using htop with hit hhit
    dsimp [term, fiber, rounds]
    rw [tsum_eq_single hit]
    · rw [Set.indicator_of_mem (by simpa using hhit.symm)]
      have huntopA : (tau omega).untopA = hit := by
        rw [← hhit]
        rfl
      rw [huntopA, ENNReal.ofReal_pow (by positivity) 2,
        ENNReal.ofReal_natCast]
      norm_cast
    · intro n hn
      rw [Set.indicator_of_notMem]
      · intro hmem
        have heq : hit = n := by
          simpa using hhit.trans hmem
        exact hn heq.symm
  calc
    (∑' n : Nat,
        ((((n + 1) ^ 2 : Nat) : ENNReal) * mu (fiber n))) =
        ∑' n : Nat, ∫⁻ omega, term n omega ∂mu := by
          apply tsum_congr
          intro n
          exact (htermIntegral n).symm
    _ = ∫⁻ omega, ∑' n : Nat, term n omega ∂mu := by
      rw [lintegral_tsum htermMeasurable]
    _ = ∫⁻ omega, ENNReal.ofReal (rounds omega ^ 2) ∂mu :=
      lintegral_congr_ae hpoint
    _ = ∫⁻ omega,
        ENNReal.ofReal
          (((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) ∂mu := rfl

/-- The equality fibers of an a.e.-finite L2 stopping time have finite total
mass after weighting by the squared successor index. -/
theorem tsum_natSuccSquare_mul_stoppingFiberMeasure_ne_top
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (hfinite : ∀ᵐ omega ∂mu, tau omega ≠ ⊤)
    (hrounds :
      MemLp (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) 2 mu) :
    Ne (∑' n : Nat,
      ((((n + 1) ^ 2 : Nat) : ENNReal) *
        mu {omega | tau omega = (n : WithTop Nat)})) ∞ := by
  rw [tsum_natSuccSquare_mul_stoppingFiberMeasure_eq_lintegral_rounds_sq
    mu tau htau hfinite]
  have hroundsFinite :
      ∫⁻ omega,
          ENNReal.ofReal
            (((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) ∂mu < ∞ := by
    rw [← hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact hrounds.integrable_sq.hasFiniteIntegral
  exact hroundsFinite.ne

/-- The real weighted fiber sum is exactly the second moment of the
successor-round count. -/
theorem tsum_natSuccSquare_mul_stoppingFiberRealMeasure_eq_integral_rounds_sq
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (hfinite : ∀ᵐ omega ∂mu, tau omega ≠ ⊤)
    (hrounds :
      MemLp (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) 2 mu) :
    (∑' n : Nat,
        (((n + 1 : Nat) : Real) ^ 2) *
          mu.real {omega | tau omega = (n : WithTop Nat)}) =
      integral mu
        (fun omega =>
          ((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) := by
  calc
    (∑' n : Nat,
        (((n + 1 : Nat) : Real) ^ 2) *
          mu.real {omega | tau omega = (n : WithTop Nat)}) =
        (∑' n : Nat,
          ((((n + 1) ^ 2 : Nat) : ENNReal) *
            mu {omega | tau omega = (n : WithTop Nat)})).toReal := by
      rw [ENNReal.tsum_toReal_eq (fun n =>
        ENNReal.mul_ne_top (by simp) (measure_ne_top mu _))]
      apply tsum_congr
      intro n
      rw [ENNReal.toReal_mul, measureReal_def]
      norm_cast
    _ = (∫⁻ omega,
          ENNReal.ofReal
            (((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) ∂mu).toReal := by
      rw [tsum_natSuccSquare_mul_stoppingFiberMeasure_eq_lintegral_rounds_sq
        mu tau htau hfinite]
    _ = integral mu
        (fun omega =>
          ((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) := by
      symm
      exact integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        hrounds.integrable_sq.aestronglyMeasurable

/-- The square roots of the real equality-fiber masses are summable for an
a.e.-finite stopping time whose successor round count belongs to `L2`. -/
theorem summable_sqrt_stoppingFiberRealMeasure_of_memLp_two
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (hfinite : ∀ᵐ omega ∂mu, tau omega ≠ ⊤)
    (hrounds :
      MemLp (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) 2 mu) :
    Summable (fun n : Nat =>
      Real.sqrt (mu.real {omega | tau omega = (n : WithTop Nat)})) := by
  let fiber : Nat -> Set Omega := fun n =>
    {omega | tau omega = (n : WithTop Nat)}
  have hweightedTop :
      Ne (∑' n : Nat,
        ((((n + 1) ^ 2 : Nat) : ENNReal) * mu (fiber n))) ∞ := by
    simpa only [fiber] using
      tsum_natSuccSquare_mul_stoppingFiberMeasure_ne_top
        mu tau htau hfinite hrounds
  have hweightedReal : Summable (fun n : Nat =>
      (((n + 1 : Nat) : Real) ^ 2) * mu.real (fiber n)) := by
    have htoReal := ENNReal.summable_toReal hweightedTop
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      measureReal_def, Nat.cast_pow] using htoReal
  have hinverseSquare : Summable (fun n : Nat =>
      1 / (((n + 1 : Nat) : Real) ^ 2)) := by
    let base : Nat -> Real := fun n => 1 / ((n : Real) ^ 2)
    have hbase : Summable base := by
      exact Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa [base] using
      ((summable_nat_add_iff (f := base) 1).2 hbase)
  have hmajorant : Summable (fun n : Nat =>
      (1 / 2 : Real) *
        ((((n + 1 : Nat) : Real) ^ 2) * mu.real (fiber n) +
          1 / (((n + 1 : Nat) : Real) ^ 2))) :=
    (hweightedReal.add hinverseSquare).mul_left (1 / 2 : Real)
  apply hmajorant.of_nonneg_of_le
  · intro n
    exact Real.sqrt_nonneg _
  · intro n
    let x : Real := ((n + 1 : Nat) : Real)
    let p : Real := mu.real (fiber n)
    change Real.sqrt p <= (1 / 2 : Real) * (x ^ 2 * p + 1 / x ^ 2)
    have hx : 0 < x := by
      dsimp [x]
      positivity
    have hp : 0 <= p := by
      dsimp [p]
      exact measureReal_nonneg
    have hsqrtSq : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp
    have hxInv : x * (1 / x) = 1 := by
      field_simp
    have hyoung := sq_nonneg (x * Real.sqrt p - 1 / x)
    have hyoungIdentity :
        (x * Real.sqrt p - 1 / x) ^ 2 =
          x ^ 2 * p - 2 * Real.sqrt p + (1 / x) ^ 2 := by
      calc
        (x * Real.sqrt p - 1 / x) ^ 2 =
            x ^ 2 * (Real.sqrt p) ^ 2 -
              2 * (x * (1 / x)) * Real.sqrt p + (1 / x) ^ 2 := by
                ring
        _ = x ^ 2 * p - 2 * Real.sqrt p + (1 / x) ^ 2 := by
          rw [hsqrtSq, hxInv]
          ring
    rw [hyoungIdentity] at hyoung
    have hraw :
        2 * Real.sqrt p <= x ^ 2 * p + (1 / x) ^ 2 := by
      nlinarith
    have hinvSq : (1 / x) ^ 2 = 1 / x ^ 2 := by ring
    rw [← hinvSq]
    nlinarith

/-- The square-root fiber-mass sum is quantitatively controlled by one half
of the stopping-round second moment plus the universal inverse-square series.
This is a fixed-stopping-time estimate, not a uniform family bound. -/
theorem
    tsum_sqrt_stoppingFiberRealMeasure_le_half_mul_integral_rounds_sq_add_tsum_inverse_natSuccSquare_of_memLp_two
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (hfinite : ∀ᵐ omega ∂mu, tau omega ≠ ⊤)
    (hrounds :
      MemLp (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) 2 mu) :
    (∑' n : Nat,
        Real.sqrt (mu.real {omega | tau omega = (n : WithTop Nat)})) <=
      (1 / 2 : Real) *
        (integral mu
            (fun omega =>
              ((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) +
          ∑' n : Nat, 1 / (((n + 1 : Nat) : Real) ^ 2)) := by
  let fiber : Nat -> Set Omega := fun n =>
    {omega | tau omega = (n : WithTop Nat)}
  have hweightedTop :
      Ne (∑' n : Nat,
        ((((n + 1) ^ 2 : Nat) : ENNReal) * mu (fiber n))) ∞ := by
    simpa only [fiber] using
      tsum_natSuccSquare_mul_stoppingFiberMeasure_ne_top
        mu tau htau hfinite hrounds
  have hweighted : Summable (fun n : Nat =>
      (((n + 1 : Nat) : Real) ^ 2) * mu.real (fiber n)) := by
    have htoReal := ENNReal.summable_toReal hweightedTop
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      measureReal_def, Nat.cast_pow] using htoReal
  have hinverseSquare : Summable (fun n : Nat =>
      1 / (((n + 1 : Nat) : Real) ^ 2)) := by
    let base : Nat -> Real := fun n => 1 / ((n : Real) ^ 2)
    have hbase : Summable base := by
      exact Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa [base] using
      ((summable_nat_add_iff (f := base) 1).2 hbase)
  have hmajorant : Summable (fun n : Nat =>
      (1 / 2 : Real) *
        ((((n + 1 : Nat) : Real) ^ 2) * mu.real (fiber n) +
          1 / (((n + 1 : Nat) : Real) ^ 2))) :=
    (hweighted.add hinverseSquare).mul_left (1 / 2 : Real)
  have hpoint (n : Nat) :
      Real.sqrt (mu.real (fiber n)) <=
        (1 / 2 : Real) *
          ((((n + 1 : Nat) : Real) ^ 2) * mu.real (fiber n) +
            1 / (((n + 1 : Nat) : Real) ^ 2)) := by
    let x : Real := ((n + 1 : Nat) : Real)
    let p : Real := mu.real (fiber n)
    change Real.sqrt p <= (1 / 2 : Real) * (x ^ 2 * p + 1 / x ^ 2)
    have hx : 0 < x := by
      dsimp [x]
      positivity
    have hp : 0 <= p := by
      dsimp [p]
      exact measureReal_nonneg
    have hsqrtSq : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp
    have hxInv : x * (1 / x) = 1 := by
      field_simp
    have hyoung := sq_nonneg (x * Real.sqrt p - 1 / x)
    have hyoungIdentity :
        (x * Real.sqrt p - 1 / x) ^ 2 =
          x ^ 2 * p - 2 * Real.sqrt p + (1 / x) ^ 2 := by
      calc
        (x * Real.sqrt p - 1 / x) ^ 2 =
            x ^ 2 * (Real.sqrt p) ^ 2 -
              2 * (x * (1 / x)) * Real.sqrt p + (1 / x) ^ 2 := by
                ring
        _ = x ^ 2 * p - 2 * Real.sqrt p + (1 / x) ^ 2 := by
          rw [hsqrtSq, hxInv]
          ring
    rw [hyoungIdentity] at hyoung
    have hraw :
        2 * Real.sqrt p <= x ^ 2 * p + (1 / x) ^ 2 := by
      nlinarith
    have hinvSq : (1 / x) ^ 2 = 1 / x ^ 2 := by ring
    rw [← hinvSq]
    nlinarith
  have hsqrt :=
    summable_sqrt_stoppingFiberRealMeasure_of_memLp_two
      mu tau htau hfinite hrounds
  calc
    (∑' n : Nat,
        Real.sqrt (mu.real {omega | tau omega = (n : WithTop Nat)})) <=
        ∑' n : Nat,
          (1 / 2 : Real) *
            ((((n + 1 : Nat) : Real) ^ 2) * mu.real (fiber n) +
              1 / (((n + 1 : Nat) : Real) ^ 2)) := by
      simpa only [fiber] using hsqrt.tsum_le_tsum hpoint hmajorant
    _ = (1 / 2 : Real) *
        ((∑' n : Nat,
            (((n + 1 : Nat) : Real) ^ 2) * mu.real (fiber n)) +
          ∑' n : Nat, 1 / (((n + 1 : Nat) : Real) ^ 2)) := by
      rw [tsum_mul_left, Summable.tsum_add hweighted hinverseSquare]
    _ = (1 / 2 : Real) *
        (integral mu
            (fun omega =>
              ((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) +
          ∑' n : Nat, 1 / (((n + 1 : Nat) : Real) ^ 2)) := by
      rw [show
        (∑' n : Nat,
            (((n + 1 : Nat) : Real) ^ 2) * mu.real (fiber n)) =
          integral mu
            (fun omega =>
              ((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) by
        simpa only [fiber] using
          tsum_natSuccSquare_mul_stoppingFiberRealMeasure_eq_integral_rounds_sq
            mu tau htau hfinite hrounds]

/-- Cauchy--Schwarz controls the square-root stopping-fiber masses by the
actual successor-round second moment and the shifted inverse-square series.
This is a fixed-stopping-time estimate, not a uniform family bound. -/
theorem
    tsum_sqrt_stoppingFiberRealMeasure_le_sqrt_integral_rounds_sq_mul_sqrt_tsum_inverse_natSuccSquare_of_memLp_two
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (hfinite : ∀ᵐ omega ∂mu, tau omega ≠ ⊤)
    (hrounds :
      MemLp (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) 2 mu) :
    (∑' n : Nat,
        Real.sqrt (mu.real {omega | tau omega = (n : WithTop Nat)})) <=
      Real.sqrt
          (integral mu
            (fun omega =>
              ((((tau omega).untopA + 1 : Nat) : Real)) ^ 2)) *
        Real.sqrt (∑' n : Nat, 1 / (((n + 1 : Nat) : Real) ^ 2)) := by
  let fiber : Nat -> Set Omega := fun n =>
    {omega | tau omega = (n : WithTop Nat)}
  have hsqrtSummable : Summable (fun n : Nat =>
      Real.sqrt (mu.real (fiber n))) := by
    simpa only [fiber] using
      summable_sqrt_stoppingFiberRealMeasure_of_memLp_two
        mu tau htau hfinite hrounds
  have hweighted : Summable (fun n : Nat =>
      (((n + 1 : Nat) : Real) ^ 2) * mu.real (fiber n)) := by
    have hweightedTop :=
      tsum_natSuccSquare_mul_stoppingFiberMeasure_ne_top
        mu tau htau hfinite hrounds
    have htoReal := ENNReal.summable_toReal hweightedTop
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      measureReal_def, Nat.cast_pow] using htoReal
  have hinverseSquare : Summable (fun n : Nat =>
      1 / (((n + 1 : Nat) : Real) ^ 2)) := by
    let base : Nat -> Real := fun n => 1 / ((n : Real) ^ 2)
    have hbase : Summable base :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa [base] using ((summable_nat_add_iff (f := base) 1).2 hbase)
  have hfiniteSum (s : Finset Nat) :
      ∑ n ∈ s, Real.sqrt (mu.real (fiber n)) <=
        Real.sqrt
            (∑ n ∈ s,
              (((n + 1 : Nat) : Real) ^ 2) * mu.real (fiber n)) *
          Real.sqrt
            (∑ n ∈ s, 1 / (((n + 1 : Nat) : Real) ^ 2)) := by
    let x : Nat -> Real := fun n => ((n + 1 : Nat) : Real)
    let p : Nat -> Real := fun n => mu.real (fiber n)
    have hterm (n : Nat) :
        Real.sqrt (p n) =
          (x n * Real.sqrt (p n)) * (1 / x n) := by
      have hx : x n ≠ 0 := by
        dsimp [x]
        positivity
      field_simp
    have hfSq (n : Nat) :
        (x n * Real.sqrt (p n)) ^ 2 = x n ^ 2 * p n := by
      rw [mul_pow, Real.sq_sqrt]
      dsimp [p]
      exact measureReal_nonneg
    have hgSq (n : Nat) : (1 / x n) ^ 2 = 1 / x n ^ 2 := by
      ring
    calc
      ∑ n ∈ s, Real.sqrt (mu.real (fiber n)) =
          ∑ n ∈ s, (x n * Real.sqrt (p n)) * (1 / x n) := by
            apply Finset.sum_congr rfl
            intro n hn
            simpa only [p] using hterm n
      _ <=
          Real.sqrt (∑ n ∈ s, (x n * Real.sqrt (p n)) ^ 2) *
            Real.sqrt (∑ n ∈ s, (1 / x n) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s
          (fun n => x n * Real.sqrt (p n)) (fun n => 1 / x n)
      _ =
          Real.sqrt
              (∑ n ∈ s,
                (((n + 1 : Nat) : Real) ^ 2) * mu.real (fiber n)) *
            Real.sqrt
              (∑ n ∈ s, 1 / (((n + 1 : Nat) : Real) ^ 2)) := by
        simp only [hfSq, hgSq, x, p]
  have hsumBound (s : Finset Nat) :
      ∑ n ∈ s, Real.sqrt (mu.real (fiber n)) <=
        Real.sqrt
            (∑' n : Nat,
              (((n + 1 : Nat) : Real) ^ 2) * mu.real (fiber n)) *
          Real.sqrt (∑' n : Nat,
            1 / (((n + 1 : Nat) : Real) ^ 2)) := by
    refine (hfiniteSum s).trans ?_
    apply mul_le_mul
    · apply Real.sqrt_le_sqrt
      exact hweighted.sum_le_tsum s (fun n hn =>
        mul_nonneg (sq_nonneg _) measureReal_nonneg)
    · apply Real.sqrt_le_sqrt
      exact hinverseSquare.sum_le_tsum s (fun n hn => by positivity)
    · exact Real.sqrt_nonneg _
    · exact Real.sqrt_nonneg _
  have htsum := hsqrtSummable.tsum_le_of_sum_le hsumBound
  rw [tsum_natSuccSquare_mul_stoppingFiberRealMeasure_eq_integral_rounds_sq
    mu tau htau hfinite hrounds] at htsum
  simpa only [fiber] using htsum

/-- Uniform deterministic-coordinate second moments and an L2 finite stopping
time make the corresponding unbounded stopped value integrable. The proof is
a countable equality-fiber decomposition; it does not use optional stopping. -/
theorem integrable_stoppedValue_of_uniform_secondMoment_of_memLp_two_rounds
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (hfinite : ∀ᵐ omega ∂mu, tau omega ≠ ⊤)
    (hrounds :
      MemLp (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) 2 mu)
    (process : Nat -> Omega -> Real)
    (hstoppedMeasurable : Measurable (stoppedValue process tau))
    (secondMomentEnvelope : Real)
    (hprocessMemLp : ∀ n, MemLp (process n) 2 mu)
    (hprocessSecondMoment : ∀ n,
      integral mu (fun omega => process n omega ^ 2) <=
        secondMomentEnvelope) :
    Integrable (stoppedValue process tau) mu := by
  let fiber : Nat -> Set Omega := fun n =>
    {omega | tau omega = (n : WithTop Nat)}
  let term : Nat -> Omega -> ENNReal := fun n =>
    (fiber n).indicator (fun omega => ENNReal.ofReal |process n omega|)
  let majorant : Nat -> Real := fun n =>
    Real.sqrt secondMomentEnvelope * Real.sqrt (mu.real (fiber n))
  have hfiberMeasurable (n : Nat) : MeasurableSet (fiber n) := by
    exact measurableSet_eq_fun htau measurable_const
  have htermMeasurable (n : Nat) : AEMeasurable (term n) mu := by
    exact
      (hprocessMemLp n).aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal.indicator
        (hfiberMeasurable n)
  have hmajorantSummable : Summable majorant := by
    exact
      (summable_sqrt_stoppingFiberRealMeasure_of_memLp_two
        mu tau htau hfinite hrounds).mul_left
          (Real.sqrt secondMomentEnvelope)
  have hmajorantNonneg (n : Nat) : 0 <= majorant n := by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have htermIntegral (n : Nat) :
      ∫⁻ omega, term n omega ∂mu <= ENNReal.ofReal (majorant n) := by
    let restricted : Omega -> Real := fun omega =>
      (fiber n).indicator (fun omega => |process n omega|) omega
    have hrestrictedIntegrable : Integrable restricted mu := by
      exact (hprocessMemLp n).integrable (by norm_num) |>.abs.indicator
        (hfiberMeasurable n)
    have hrestrictedNonneg : ∀ omega, 0 <= restricted omega := by
      intro omega
      by_cases homega : omega ∈ fiber n <;>
        simp [restricted, homega]
    have hholder :=
      integral_indicator_le_sqrt_secondMoment_mul_sqrt_real_measure
        mu (fun omega => |process n omega|) (fun _ => abs_nonneg _)
          (hprocessMemLp n).abs (fiber n) (hfiberMeasurable n)
    have hsqrtMoment :
        Real.sqrt
            (integral mu (fun omega => |process n omega| ^ 2)) <=
          Real.sqrt secondMomentEnvelope := by
      apply Real.sqrt_le_sqrt
      simpa only [sq_abs] using hprocessSecondMoment n
    have hrealBound :
        integral mu restricted <= majorant n := by
      calc
        integral mu restricted <=
            Real.sqrt
                (integral mu (fun omega => |process n omega| ^ 2)) *
              Real.sqrt (mu.real (fiber n)) := by
                simpa only [restricted] using hholder
        _ <= Real.sqrt secondMomentEnvelope *
              Real.sqrt (mu.real (fiber n)) := by
                exact mul_le_mul_of_nonneg_right hsqrtMoment
                  (Real.sqrt_nonneg _)
        _ = majorant n := rfl
    have htermEq :
        (∫⁻ omega, term n omega ∂mu) =
          ENNReal.ofReal (integral mu restricted) := by
      rw [ofReal_integral_eq_lintegral_ofReal hrestrictedIntegrable
        (Filter.Eventually.of_forall hrestrictedNonneg)]
      apply lintegral_congr
      intro omega
      by_cases homega : omega ∈ fiber n <;>
        simp [term, restricted, homega]
    rw [htermEq]
    exact ENNReal.ofReal_le_ofReal hrealBound
  have hpoint : ∀ᵐ omega ∂mu,
      ENNReal.ofReal ‖stoppedValue process tau omega‖ =
        ∑' n : Nat, term n omega := by
    filter_upwards [hfinite] with omega htop
    lift tau omega to Nat using htop with hit hhit
    dsimp only [term, fiber]
    rw [tsum_eq_single hit]
    · rw [Set.indicator_of_mem]
      · simp only [stoppedValue, Real.norm_eq_abs]
        have huntopA : (tau omega).untopA = hit := by
          rw [← hhit]
          rfl
        rw [huntopA]
      · exact hhit.symm
    · intro n hn
      rw [Set.indicator_of_notMem]
      intro hmem
      have heq : hit = n := by
        simpa using hhit.trans hmem
      exact hn heq.symm
  have hsumFinite :
      (∑' n : Nat, ∫⁻ omega, term n omega ∂mu) < ⊤ := by
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum htermIntegral)
    exact lt_top_iff_ne_top.mpr hmajorantSummable.tsum_ofReal_ne_top
  refine ⟨hstoppedMeasurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc
    ∫⁻ omega, ENNReal.ofReal ‖stoppedValue process tau omega‖ ∂mu =
        ∫⁻ omega, ∑' n : Nat, term n omega ∂mu :=
      lintegral_congr_ae hpoint
    _ = ∑' n : Nat, ∫⁻ omega, term n omega ∂mu := by
      rw [lintegral_tsum htermMeasurable]
    _ < ⊤ := hsumFinite

/-- A quantitative version of the stopping-fiber transport: the absolute
first moment of the stopped value is bounded by the uniform coordinate L2
envelope times the sum of square roots of the stopping-fiber masses. This is
a fixed-stopping-time bound, not an index-uniform rate or optional stopping. -/
theorem
    integral_abs_stoppedValue_le_uniformSecondMoment_mul_tsum_sqrt_stoppingFiberRealMeasure_of_memLp_two_rounds
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (hfinite : ∀ᵐ omega ∂mu, tau omega ≠ ⊤)
    (hrounds :
      MemLp (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) 2 mu)
    (process : Nat -> Omega -> Real)
    (secondMomentEnvelope : Real)
    (hprocessMemLp : ∀ n, MemLp (process n) 2 mu)
    (hprocessSecondMoment : ∀ n,
      integral mu (fun omega => process n omega ^ 2) <=
        secondMomentEnvelope) :
    integral mu (fun omega => |stoppedValue process tau omega|) <=
      Real.sqrt secondMomentEnvelope *
        ∑' n : Nat,
          Real.sqrt (mu.real {omega | tau omega = (n : WithTop Nat)}) := by
  let fiber : Nat -> Set Omega := fun n =>
    {omega | tau omega = (n : WithTop Nat)}
  let term : Nat -> Omega -> Real := fun n =>
    (fiber n).indicator (fun omega => |process n omega|)
  let majorant : Nat -> Real := fun n =>
    Real.sqrt secondMomentEnvelope * Real.sqrt (mu.real (fiber n))
  have hfiberMeasurable (n : Nat) : MeasurableSet (fiber n) := by
    exact measurableSet_eq_fun htau measurable_const
  have htermIntegrable (n : Nat) : Integrable (term n) mu := by
    dsimp only [term]
    exact (hprocessMemLp n).integrable (by norm_num) |>.abs.indicator
      (hfiberMeasurable n)
  have htermNonneg (n : Nat) (omega : Omega) : 0 <= term n omega := by
    by_cases homega : omega ∈ fiber n <;>
      simp [term, homega]
  have hmajorantSummable : Summable majorant := by
    exact
      (summable_sqrt_stoppingFiberRealMeasure_of_memLp_two
        mu tau htau hfinite hrounds).mul_left
          (Real.sqrt secondMomentEnvelope)
  have htermIntegral (n : Nat) :
      integral mu (term n) <= majorant n := by
    have hholder :=
      integral_indicator_le_sqrt_secondMoment_mul_sqrt_real_measure
        mu (fun omega => |process n omega|) (fun _ => abs_nonneg _)
          (hprocessMemLp n).abs (fiber n) (hfiberMeasurable n)
    have hsqrtMoment :
        Real.sqrt
            (integral mu (fun omega => |process n omega| ^ 2)) <=
          Real.sqrt secondMomentEnvelope := by
      apply Real.sqrt_le_sqrt
      simpa only [sq_abs] using hprocessSecondMoment n
    calc
      integral mu (term n) <=
          Real.sqrt
              (integral mu (fun omega => |process n omega| ^ 2)) *
            Real.sqrt (mu.real (fiber n)) := by
              simpa only [term] using hholder
      _ <= Real.sqrt secondMomentEnvelope *
            Real.sqrt (mu.real (fiber n)) := by
              exact mul_le_mul_of_nonneg_right hsqrtMoment
                (Real.sqrt_nonneg _)
      _ = majorant n := rfl
  have hnormIntegralEq (n : Nat) :
      integral mu (fun omega => ‖term n omega‖) = integral mu (term n) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun omega => by
      change ‖term n omega‖ = term n omega
      rw [Real.norm_eq_abs, abs_of_nonneg (htermNonneg n omega)]
  have htermIntegralNormSummable :
      Summable (fun n => integral mu (fun omega => ‖term n omega‖)) := by
    apply hmajorantSummable.of_nonneg_of_le
    · intro n
      exact integral_nonneg fun omega => norm_nonneg (term n omega)
    · intro n
      rw [hnormIntegralEq]
      exact htermIntegral n
  have htermIntegralSummable :
      Summable (fun n => integral mu (term n)) := by
    simpa only [hnormIntegralEq] using htermIntegralNormSummable
  have hpoint : ∀ᵐ omega ∂mu,
      |stoppedValue process tau omega| = ∑' n : Nat, term n omega := by
    filter_upwards [hfinite] with omega htop
    lift tau omega to Nat using htop with hit hhit
    dsimp only [term, fiber]
    rw [tsum_eq_single hit]
    · rw [Set.indicator_of_mem]
      · simp only [stoppedValue]
        have huntopA : (tau omega).untopA = hit := by
          rw [← hhit]
          rfl
        rw [huntopA]
      · exact hhit.symm
    · intro n hn
      rw [Set.indicator_of_notMem]
      intro hmem
      have heq : hit = n := by
        simpa using hhit.trans hmem
      exact hn heq.symm
  calc
    integral mu (fun omega => |stoppedValue process tau omega|) =
        integral mu (fun omega => ∑' n : Nat, term n omega) :=
      integral_congr_ae hpoint
    _ = ∑' n : Nat, integral mu (term n) :=
      (integral_tsum_of_summable_integral_norm
        htermIntegrable htermIntegralNormSummable).symm
    _ <= ∑' n : Nat, majorant n :=
      htermIntegralSummable.tsum_le_tsum htermIntegral hmajorantSummable
    _ = Real.sqrt secondMomentEnvelope *
          ∑' n : Nat, Real.sqrt (mu.real (fiber n)) := by
      rw [tsum_mul_left]
    _ = Real.sqrt secondMomentEnvelope *
          ∑' n : Nat,
            Real.sqrt (mu.real {omega | tau omega = (n : WithTop Nat)}) := rfl

/-- The stopped-value first moment inherits the Cauchy--Schwarz stopping-fiber
bound. The estimate is for one fixed stopping time and does not invoke
optional stopping. -/
theorem
    integral_abs_stoppedValue_le_uniformSecondMoment_mul_sqrt_integral_rounds_sq_mul_sqrt_tsum_inverse_natSuccSquare_of_memLp_two_rounds
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (hfinite : ∀ᵐ omega ∂mu, tau omega ≠ ⊤)
    (hrounds :
      MemLp (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) 2 mu)
    (process : Nat -> Omega -> Real)
    (secondMomentEnvelope : Real)
    (hprocessMemLp : ∀ n, MemLp (process n) 2 mu)
    (hprocessSecondMoment : ∀ n,
      integral mu (fun omega => process n omega ^ 2) <=
        secondMomentEnvelope) :
    integral mu (fun omega => |stoppedValue process tau omega|) <=
      Real.sqrt secondMomentEnvelope *
        (Real.sqrt
            (integral mu
              (fun omega =>
                ((((tau omega).untopA + 1 : Nat) : Real)) ^ 2)) *
          Real.sqrt (∑' n : Nat,
            1 / (((n + 1 : Nat) : Real) ^ 2))) := by
  calc
    integral mu (fun omega => |stoppedValue process tau omega|) <=
        Real.sqrt secondMomentEnvelope *
          ∑' n : Nat,
            Real.sqrt (mu.real {omega | tau omega = (n : WithTop Nat)}) :=
      integral_abs_stoppedValue_le_uniformSecondMoment_mul_tsum_sqrt_stoppingFiberRealMeasure_of_memLp_two_rounds
        mu tau htau hfinite hrounds process secondMomentEnvelope
          hprocessMemLp hprocessSecondMoment
    _ <=
        Real.sqrt secondMomentEnvelope *
          (Real.sqrt
              (integral mu
                (fun omega =>
                  ((((tau omega).untopA + 1 : Nat) : Real)) ^ 2)) *
            Real.sqrt (∑' n : Nat,
              1 / (((n + 1 : Nat) : Real) ^ 2))) := by
      apply mul_le_mul_of_nonneg_left
      · exact
          tsum_sqrt_stoppingFiberRealMeasure_le_sqrt_integral_rounds_sq_mul_sqrt_tsum_inverse_natSuccSquare_of_memLp_two
            mu tau htau hfinite hrounds
      · exact Real.sqrt_nonneg _

/-- The stopping-fiber absolute first-moment estimate with its fiber sum
eliminated in favor of the actual successor-round second moment and the
universal inverse-square series. -/
theorem
    integral_abs_stoppedValue_le_uniformSecondMoment_mul_half_roundSecondMoment_add_inverseSquareTsum_of_memLp_two_rounds
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (hfinite : ∀ᵐ omega ∂mu, tau omega ≠ ⊤)
    (hrounds :
      MemLp (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) 2 mu)
    (process : Nat -> Omega -> Real)
    (secondMomentEnvelope : Real)
    (hprocessMemLp : ∀ n, MemLp (process n) 2 mu)
    (hprocessSecondMoment : ∀ n,
      integral mu (fun omega => process n omega ^ 2) <=
        secondMomentEnvelope) :
    integral mu (fun omega => |stoppedValue process tau omega|) <=
      Real.sqrt secondMomentEnvelope *
        ((1 / 2 : Real) *
          (integral mu
              (fun omega =>
                ((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) +
            ∑' n : Nat, 1 / (((n + 1 : Nat) : Real) ^ 2))) := by
  calc
    integral mu (fun omega => |stoppedValue process tau omega|) <=
        Real.sqrt secondMomentEnvelope *
          ∑' n : Nat,
            Real.sqrt
              (mu.real {omega | tau omega = (n : WithTop Nat)}) :=
      integral_abs_stoppedValue_le_uniformSecondMoment_mul_tsum_sqrt_stoppingFiberRealMeasure_of_memLp_two_rounds
        mu tau htau hfinite hrounds process secondMomentEnvelope
          hprocessMemLp hprocessSecondMoment
    _ <= Real.sqrt secondMomentEnvelope *
        ((1 / 2 : Real) *
          (integral mu
              (fun omega =>
                ((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) +
            ∑' n : Nat, 1 / (((n + 1 : Nat) : Real) ^ 2))) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_sqrt_stoppingFiberRealMeasure_le_half_mul_integral_rounds_sq_add_tsum_inverse_natSuccSquare_of_memLp_two
          mu tau htau hfinite hrounds)
        (Real.sqrt_nonneg _)

end BanditRLProof
