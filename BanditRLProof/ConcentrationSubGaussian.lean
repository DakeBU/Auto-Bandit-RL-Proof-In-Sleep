import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import BanditRLProof.ConcentrationFixedMGF
import BanditRLProof.ConcentrationQuadraticFixedMGF
import BanditRLProof.ProbabilityUnionBound

namespace ProbabilityTheory

/--
Transport a conditional sub-Gaussian witness across equality of the
conditioning measurable spaces.

The two sub-sigma-algebra proofs are propositionally irrelevant once the
measurable spaces are identified. This is a general-purpose adapter for
filtrations presented through different but extensionally equal histories.
-/
theorem HasCondSubgaussianMGF.of_measurableSpace_eq
    {Omega : Type u} {m0 m1 mOmega : MeasurableSpace Omega}
    [StandardBorelSpace Omega]
    {mu : MeasureTheory.Measure Omega} [MeasureTheory.IsFiniteMeasure mu]
    {X : Omega -> Real} {c : NNReal}
    (hm0 : m0 <= mOmega) (hm1 : m1 <= mOmega)
    (hm : m0 = m1)
    (hX : HasCondSubgaussianMGF m0 hm0 X c mu) :
    HasCondSubgaussianMGF m1 hm1 X c mu := by
  subst m1
  simpa only using hX

/--
A conditionally sub-Gaussian variable remains conditionally sub-Gaussian with
the same proxy after restriction to an event measurable in the conditioning
sigma-algebra.

The proof uses one common exceptional set for every exponential tilt: the
conditional-expectation kernel is supported on the current side of a
conditioning-measurable event, so the indicator-masked variable is kernel-a.e.
equal either to the original variable or to zero.
-/
theorem HasCondSubgaussianMGF.indicator
    {Omega : Type u} {m mOmega : MeasurableSpace Omega}
    [StandardBorelSpace Omega]
    {mu : MeasureTheory.Measure Omega}
    [MeasureTheory.IsProbabilityMeasure mu]
    {X : Omega -> Real} {c : NNReal}
    (hm : m <= mOmega)
    (hX : HasCondSubgaussianMGF m hm X c mu)
    {s : Set Omega} (hs : @MeasurableSet Omega m s) :
    HasCondSubgaussianMGF m hm (s.indicator X) c mu := by
  let kappa := ProbabilityTheory.condExpKernel mu m
  have hsOmega : MeasurableSet s := hm s hs
  have hcond_mu :
      MeasureTheory.condExp m mu
          (s.indicator (fun _ : Omega => (1 : Real))) =ᵐ[mu]
        s.indicator (fun _ : Omega => (1 : Real)) := by
    simpa [MeasureTheory.condExp_const hm] using
      (MeasureTheory.condExp_indicator
        (μ := mu) (m := m) (f := fun _ : Omega => (1 : Real))
        (MeasureTheory.integrable_const (1 : Real)) hs)
  have hcond_trim :
      MeasureTheory.condExp m mu
          (s.indicator (fun _ : Omega => (1 : Real))) =ᵐ[mu.trim hm]
        s.indicator (fun _ : Omega => (1 : Real)) := by
    exact
      MeasureTheory.StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable
        hm MeasureTheory.stronglyMeasurable_condExp
        (MeasureTheory.stronglyMeasurable_const.indicator hs) hcond_mu
  have hkernel_real :=
    ProbabilityTheory.condExpKernel_ae_eq_trim_condExp
      (μ := mu) hm hsOmega
  change ProbabilityTheory.Kernel.HasSubgaussianMGF
    (s.indicator X) c kappa (mu.trim hm)
  refine ⟨?_, ?_⟩
  · intro t
    rw [show kappa ∘ₘ (mu.trim hm) = mu by
      simpa [kappa] using
        (ProbabilityTheory.condExpKernel_comp_trim (μ := mu) hm)]
    have hmasked :
        (fun omega => Real.exp (t * s.indicator X omega)) =
          (fun omega =>
            s.indicator (fun y => Real.exp (t * X y)) omega +
              sᶜ.indicator (fun _ => (1 : Real)) omega) := by
      funext omega
      by_cases homega : omega ∈ s
      · simp [homega]
      · simp [homega]
    rw [hmasked]
    exact
      ((hX.integrable_exp_mul t).indicator hsOmega).add
        ((MeasureTheory.integrable_const (1 : Real)).indicator hsOmega.compl)
  · filter_upwards [hX.mgf_le, hkernel_real, hcond_trim] with
      omega hmgf hkernel hcond
    letI : MeasureTheory.IsProbabilityMeasure (kappa omega) := by
      dsimp [kappa]
      infer_instance
    intro t
    by_cases homega : omega ∈ s
    · have hmeasure_s : kappa omega s = 1 := by
        apply (ENNReal.toReal_eq_one_iff (kappa omega s)).mp
        change (kappa omega).real s = 1
        rw [hkernel, hcond]
        simp [Set.indicator_of_mem homega]
      have hmeasure_compl : kappa omega sᶜ = 0 := by
        rw [MeasureTheory.measure_compl hsOmega (by finiteness), hmeasure_s]
        simp
      have hmasked : s.indicator X =ᵐ[kappa omega] X := by
        apply MeasureTheory.ae_iff.mpr
        apply MeasureTheory.measure_mono_null _ hmeasure_compl
        intro y hy
        change y ∉ s
        intro hyMem
        exact hy (by simp [Set.indicator_of_mem hyMem])
      rw [ProbabilityTheory.mgf_congr hmasked]
      exact hmgf t
    · have hmeasure_s : kappa omega s = 0 := by
        apply (MeasureTheory.measureReal_eq_zero_iff).mp
        rw [hkernel, hcond]
        simp [Set.indicator_of_notMem homega]
      have hmasked :
          s.indicator X =ᵐ[kappa omega] (fun _ : Omega => (0 : Real)) := by
        apply MeasureTheory.ae_iff.mpr
        apply MeasureTheory.measure_mono_null _ hmeasure_s
        intro y hy
        by_contra hyMem
        exact hy (by simp [Set.indicator_of_notMem hyMem])
      rw [ProbabilityTheory.mgf_congr hmasked, ProbabilityTheory.mgf_const]
      have hc : 0 <= (c : Real) := NNReal.coe_nonneg c
      have ht : 0 <= t ^ 2 := sq_nonneg t
      have htwo : (0 : Real) <= 2 := by norm_num
      simpa using Real.one_le_exp
        (div_nonneg (mul_nonneg hc ht) htwo)

/--
At a fixed tilt, a conditioning-measurable mask pays the sub-Gaussian
quadratic budget only on the masked event.  This is the one-step predictable
variance interface needed for count-sensitive adaptive-sampling tails.
-/
theorem HasCondSubgaussianMGF.indicator_compensated_hasCondMGFUpperBoundAt
    {Omega : Type u} {m mOmega : MeasurableSpace Omega}
    [StandardBorelSpace Omega]
    {mu : MeasureTheory.Measure Omega}
    [MeasureTheory.IsProbabilityMeasure mu]
    {X : Omega -> Real} {c : NNReal}
    (hm : m <= mOmega)
    (hX : HasCondSubgaussianMGF m hm X c mu)
    {s : Set Omega} (hs : @MeasurableSet Omega m s)
    (tilt : Real) :
    BanditRLProof.Concentration.HasCondMGFUpperBoundAt m hm
      (fun omega =>
        tilt * s.indicator X omega -
          (((c : NNReal) : Real) * tilt ^ 2 / 2) *
            s.indicator (fun _ : Omega => (1 : Real)) omega)
      1 0 mu := by
  let kappa := ProbabilityTheory.condExpKernel mu m
  let q : Real := (((c : NNReal) : Real) * tilt ^ 2 / 2)
  have hsOmega : MeasurableSet s := hm s hs
  have hcond_mu :
      MeasureTheory.condExp m mu
          (s.indicator (fun _ : Omega => (1 : Real))) =ᵐ[mu]
        s.indicator (fun _ : Omega => (1 : Real)) := by
    simpa [MeasureTheory.condExp_const hm] using
      (MeasureTheory.condExp_indicator
        (μ := mu) (m := m) (f := fun _ : Omega => (1 : Real))
        (MeasureTheory.integrable_const (1 : Real)) hs)
  have hcond_trim :
      MeasureTheory.condExp m mu
          (s.indicator (fun _ : Omega => (1 : Real))) =ᵐ[mu.trim hm]
        s.indicator (fun _ : Omega => (1 : Real)) := by
    exact
      MeasureTheory.StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable
        hm MeasureTheory.stronglyMeasurable_condExp
        (MeasureTheory.stronglyMeasurable_const.indicator hs) hcond_mu
  have hkernel_real :=
    ProbabilityTheory.condExpKernel_ae_eq_trim_condExp
      (μ := mu) hm hsOmega
  change BanditRLProof.Concentration.Kernel.HasMGFUpperBoundAt
    (fun omega =>
      tilt * s.indicator X omega -
        (((c : NNReal) : Real) * tilt ^ 2 / 2) *
          s.indicator (fun _ : Omega => (1 : Real)) omega)
    1 0 kappa (mu.trim hm)
  refine ⟨?_, ?_⟩
  · intro a
    rw [show kappa ∘ₘ (mu.trim hm) = mu by
      simpa [kappa] using
        (ProbabilityTheory.condExpKernel_comp_trim (μ := mu) hm)]
    have hint :
        MeasureTheory.Integrable
          (fun omega => Real.exp (a * (tilt * X omega - q))) mu := by
      have h := (hX.integrable_exp_mul (a * tilt)).const_mul
        (Real.exp (-a * q))
      convert h using 1
      funext omega
      rw [show a * (tilt * X omega - q) =
          -a * q + (a * tilt) * X omega by ring, Real.exp_add]
    have hmasked :
        (fun omega => Real.exp
          (a * (tilt * s.indicator X omega -
            q * s.indicator (fun _ : Omega => (1 : Real)) omega))) =
          (fun omega =>
            s.indicator
                (fun y => Real.exp (a * (tilt * X y - q))) omega +
              sᶜ.indicator (fun _ => (1 : Real)) omega) := by
      funext omega
      by_cases homega : omega ∈ s
      · simp [homega]
      · simp [homega]
    rw [show (((c : NNReal) : Real) * tilt ^ 2 / 2) = q by rfl,
      hmasked]
    exact (hint.indicator hsOmega).add
      ((MeasureTheory.integrable_const (1 : Real)).indicator hsOmega.compl)
  · filter_upwards [hX.mgf_le, hkernel_real, hcond_trim] with
      omega hmgf hkernel hcond
    letI : MeasureTheory.IsProbabilityMeasure (kappa omega) := by
      dsimp [kappa]
      infer_instance
    by_cases homega : omega ∈ s
    · have hmeasure_s : kappa omega s = 1 := by
        apply (ENNReal.toReal_eq_one_iff (kappa omega s)).mp
        change (kappa omega).real s = 1
        rw [hkernel, hcond]
        simp [Set.indicator_of_mem homega]
      have hmeasure_compl : kappa omega sᶜ = 0 := by
        rw [MeasureTheory.measure_compl hsOmega (by finiteness), hmeasure_s]
        simp
      have hcomp :
          (fun y =>
            tilt * s.indicator X y -
              (((c : NNReal) : Real) * tilt ^ 2 / 2) *
                s.indicator (fun _ : Omega => (1 : Real)) y) =ᵐ[kappa omega]
            (fun y => tilt * X y - q) := by
        apply MeasureTheory.ae_iff.mpr
        apply MeasureTheory.measure_mono_null _ hmeasure_compl
        intro y hy
        change y ∉ s
        intro hyMem
        exact hy (by simp [hyMem, q])
      rw [ProbabilityTheory.mgf_congr hcomp]
      have hmgf_eq :
          ProbabilityTheory.mgf (fun y => tilt * X y - q) (kappa omega) 1 =
            Real.exp (-q) * ProbabilityTheory.mgf X (kappa omega) tilt := by
        rw [ProbabilityTheory.mgf]
        simp_rw [one_mul]
        have hfun :
            (fun y => Real.exp (tilt * X y - q)) =
              (fun y => Real.exp (-q) * Real.exp (tilt * X y)) := by
          funext y
          rw [show tilt * X y - q = -q + tilt * X y by ring,
            Real.exp_add]
        rw [hfun, MeasureTheory.integral_const_mul]
        rfl
      rw [hmgf_eq]
      calc
        Real.exp (-q) * ProbabilityTheory.mgf X (kappa omega) tilt <=
            Real.exp (-q) * Real.exp q := by
              gcongr
              simpa [q] using hmgf tilt
        _ = Real.exp 0 := by rw [← Real.exp_add]; congr 1; ring
    · have hmeasure_s : kappa omega s = 0 := by
        apply (MeasureTheory.measureReal_eq_zero_iff).mp
        rw [hkernel, hcond]
        simp [Set.indicator_of_notMem homega]
      have hcomp :
          (fun y =>
            tilt * s.indicator X y -
              (((c : NNReal) : Real) * tilt ^ 2 / 2) *
                s.indicator (fun _ : Omega => (1 : Real)) y) =ᵐ[kappa omega]
            (fun _ : Omega => (0 : Real)) := by
        apply MeasureTheory.ae_iff.mpr
        apply MeasureTheory.measure_mono_null _ hmeasure_s
        intro y hy
        by_contra hyMem
        exact hy (by simp [Set.indicator_of_notMem hyMem])
      rw [ProbabilityTheory.mgf_congr hcomp, ProbabilityTheory.mgf_const]
      simp

end ProbabilityTheory

/-!
# Sub-Gaussian concentration wrappers

This module exposes small Mathlib-backed concentration imports under the
project namespace.  It deliberately stays at the reusable tail-theorem layer:
no ETC reward model, empirical-mean construction, or final regret result is
introduced here.
-/

namespace BanditRLProof
namespace Concentration

open MeasureTheory

/--
Variance proxy induced by an almost-sure interval bound `[lo, hi]`.

This is the reusable Hoeffding proxy `(hi - lo)^2 / 4`, represented in the
same `NNReal` shape used by Mathlib's bounded-variable sub-Gaussian lemma.
-/
noncomputable def intervalVarianceProxy (lo hi : Real) : NNReal :=
  ((nnnorm (hi - lo) / 2) ^ 2)

/--
Bounded variable plus an exact mean identity gives a centered sub-Gaussian
witness.

This is the generic `TAIL-HOEFFDING-BOUNDED` import wrapper.  It keeps the
Mathlib assumptions explicit: an a.e.-measurable real variable, an a.s.
interval bound, and an equality between its integral and the supplied mean.
-/
theorem boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X : Omega -> Real} {lo hi mean : Real}
    (hmeas : AEMeasurable X mu)
    (hbound : Filter.Eventually
      (fun omega : Omega => Set.Icc lo hi (X omega)) (ae mu))
    (hmean : integral mu X = mean) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun omega : Omega => X omega - mean)
      (intervalVarianceProxy lo hi) mu := by
  have h : ProbabilityTheory.HasSubgaussianMGF
      (fun omega : Omega => X omega - integral mu X)
      (intervalVarianceProxy lo hi) mu := by
    simpa [intervalVarianceProxy] using
      (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hmeas hbound)
  refine h.congr ?_
  exact Filter.Eventually.of_forall (fun omega => by
    simp [hmean])

/--
Mathlib-backed one-sided tail bound for a finite sum of independent
sub-Gaussian real random variables.

This is the `TAIL-SUBGAUSS-SUM` import wrapper.  It is a thin project-local
surface over
`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`.
-/
theorem subGaussian_sum_tail_of_iIndepFun
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) {Idx : Type v} {X : Idx -> Omega -> Real}
    (h_indep : ProbabilityTheory.iIndepFun X mu)
    {c : Idx -> NNReal} {s : Finset Idx}
    (h_subG :
      forall i, i ∈ s ->
        ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu.real {omega | eps <= s.sum (fun i => X i omega)} <=
      Real.exp (-eps ^ 2 / (2 * ((s.sum c : NNReal) : Real))) := by
  exact ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    h_indep h_subG heps

/--
ENNReal-valued version of `subGaussian_sum_tail_of_iIndepFun`.

This is the `TAIL-SUBGAUSS-DIFF-SUM-IMPORT` boundary adapter used before an
ETC-specific reward-difference specialization exists.  The summands `X i` stay
abstract; later leaves may instantiate them with centered non-best-minus-best
exploration reward differences.
-/
theorem subGaussian_sum_tail_ennreal_of_iIndepFun
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {Idx : Type v} {X : Idx -> Omega -> Real}
    (h_indep : ProbabilityTheory.iIndepFun X mu)
    {c : Idx -> NNReal} {s : Finset Idx}
    (h_subG :
      forall i, i ∈ s ->
        ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu {omega | eps <= s.sum (fun i => X i omega)} <=
      ENNReal.ofReal
        (Real.exp (-eps ^ 2 / (2 * ((s.sum c : NNReal) : Real)))) := by
  have hreal := subGaussian_sum_tail_of_iIndepFun
    mu h_indep h_subG heps
  rw [Measure.real] at hreal
  exact (ENNReal.le_ofReal_iff_toReal_le
    (measure_ne_top mu {omega | eps <= s.sum (fun i => X i omega)})
    (Real.exp_pos _).le).2 hreal

/--
Mathlib-backed Azuma-Hoeffding tail bound for a finite prefix of a strongly
adapted conditionally sub-Gaussian process.

This is the `TAIL-COND-SUBGAUSS` import wrapper.  It keeps Mathlib's contract
visible: the zeroth summand is unconditionally sub-Gaussian, later summands are
conditionally sub-Gaussian with respect to the previous filtration level, and
the process is strongly adapted.
-/
theorem condSubGaussian_sum_tail_of_stronglyAdapted
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsZeroOrProbabilityMeasure mu]
    {Y : Nat -> Omega -> Real} {cY : Nat -> NNReal}
    {F : Filtration Nat mOmega}
    (h_adapted : StronglyAdapted F Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu)
    (n : Nat)
    (h_subG :
      forall i, i < n - 1 ->
        ProbabilityTheory.HasCondSubgaussianMGF
          (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu.real {omega | eps <= (Finset.range n).sum (fun i => Y i omega)} <=
      Real.exp (-eps ^ 2 / (2 * (((Finset.range n).sum cY : NNReal) : Real))) := by
  exact ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF
    h_adapted h0 n h_subG heps

/--
ENNReal-valued version of
`condSubGaussian_sum_tail_of_stronglyAdapted`.

This boundary adapter is shaped for later ETC conditional/filtration routes:
it preserves the same Mathlib hypotheses but returns an ordinary measure bound
against the canonical exponential RHS wrapped in `ENNReal.ofReal`.
-/
theorem condSubGaussian_sum_tail_ennreal_of_stronglyAdapted
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] [IsZeroOrProbabilityMeasure mu]
    {Y : Nat -> Omega -> Real} {cY : Nat -> NNReal}
    {F : Filtration Nat mOmega}
    (h_adapted : StronglyAdapted F Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu)
    (n : Nat)
    (h_subG :
      forall i, i < n - 1 ->
        ProbabilityTheory.HasCondSubgaussianMGF
          (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu {omega | eps <= (Finset.range n).sum (fun i => Y i omega)} <=
      ENNReal.ofReal
        (Real.exp (-eps ^ 2 / (2 * (((Finset.range n).sum cY : NNReal) : Real)))) := by
  have hreal := condSubGaussian_sum_tail_of_stronglyAdapted
    h_adapted h0 n h_subG heps
  rw [Measure.real] at hreal
  exact (ENNReal.le_ofReal_iff_toReal_le
    (measure_ne_top mu {omega | eps <= (Finset.range n).sum (fun i => Y i omega)})
    (Real.exp_pos _).le).2 hreal

/--
Two-sided ENNReal Hoeffding tail for a finite sum of independent
sub-Gaussian random variables.

Mathlib's `HasSubgaussianMGF.sum_of_iIndepFun` supplies the global sum MGF.
Upper and negated lower tails are then combined by an outer-measure union, so
no event-measurability hypothesis is needed.
-/
theorem subGaussian_sum_abs_tail_ennreal_of_iIndepFun
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {Idx : Type v} {X : Idx -> Omega -> Real}
    (h_indep : ProbabilityTheory.iIndepFun X mu)
    {c : Idx -> NNReal} {s : Finset Idx}
    (h_subG :
      forall i, i ∈ s ->
        ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu {omega | eps <= |s.sum (fun i => X i omega)|} <=
      ENNReal.ofReal
        (2 * Real.exp
          (-eps ^ 2 / (2 * ((s.sum c : NNReal) : Real)))) := by
  let S : Omega -> Real := fun omega => s.sum (fun i => X i omega)
  let variance : NNReal := s.sum c
  let tailReal : Real :=
    Real.exp (-eps ^ 2 / (2 * ((variance : NNReal) : Real)))
  have htail_nonneg : 0 <= tailReal := (Real.exp_pos _).le
  have hsum : ProbabilityTheory.HasSubgaussianMGF S variance mu := by
    simpa [S, variance] using
      (ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
        h_indep h_subG)
  have hupperReal :
      mu.real {omega | eps <= S omega} <= tailReal := by
    simpa [tailReal] using hsum.measure_ge_le heps
  have hupper :
      mu {omega | eps <= S omega} <= ENNReal.ofReal tailReal := by
    rw [Measure.real] at hupperReal
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top mu {omega | eps <= S omega}) htail_nonneg).2
      hupperReal
  have hlowerReal :
      mu.real {omega | eps <= (-S) omega} <= tailReal := by
    simpa [tailReal] using hsum.neg.measure_ge_le heps
  have hlower :
      mu {omega | eps <= (-S) omega} <= ENNReal.ofReal tailReal := by
    rw [Measure.real] at hlowerReal
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top mu {omega | eps <= (-S) omega}) htail_nonneg).2
      hlowerReal
  have hsubset :
      {omega | eps <= |S omega|} ⊆
        {omega | eps <= S omega} ∪ {omega | eps <= (-S) omega} := by
    intro omega homega
    by_cases hnonneg : 0 <= S omega
    · exact Or.inl (by simpa [abs_of_nonneg hnonneg] using homega)
    · have hnonpos : S omega <= 0 := le_of_not_ge hnonneg
      exact Or.inr (by simpa [abs_of_nonpos hnonpos] using homega)
  calc
    mu {omega | eps <= |s.sum (fun i => X i omega)|} =
        mu {omega | eps <= |S omega|} := by rfl
    _ <= mu ({omega | eps <= S omega} ∪
        {omega | eps <= (-S) omega}) := measure_mono hsubset
    _ <= mu {omega | eps <= S omega} +
        mu {omega | eps <= (-S) omega} := measure_union_le _ _
    _ <= ENNReal.ofReal tailReal + ENNReal.ofReal tailReal :=
      add_le_add hupper hlower
    _ = ENNReal.ofReal
        (2 * Real.exp
          (-eps ^ 2 / (2 * ((s.sum c : NNReal) : Real)))) := by
      rw [← ENNReal.ofReal_add htail_nonneg htail_nonneg]
      simp [tailReal, variance, two_mul]

/--
Two-sided ENNReal Azuma-Hoeffding tail for a finite prefix of a strongly
adapted conditionally sub-Gaussian process.

Mathlib first upgrades the conditional increment witnesses to a global
`HasSubgaussianMGF` witness for the finite sum.  Applying its one-sided tail to
the sum and its negation, then taking an outer-measure union bound, gives the
factor-two absolute-deviation estimate.  No event-measurability hypothesis is
needed.
-/
theorem condSubGaussian_sum_abs_tail_ennreal_of_stronglyAdapted
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] [IsZeroOrProbabilityMeasure mu]
    {Y : Nat -> Omega -> Real} {cY : Nat -> NNReal}
    {F : Filtration Nat mOmega}
    (h_adapted : StronglyAdapted F Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu)
    (n : Nat)
    (h_subG :
      forall i, i < n - 1 ->
        ProbabilityTheory.HasCondSubgaussianMGF
          (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu {omega |
        eps <= |(Finset.range n).sum (fun i => Y i omega)|} <=
      ENNReal.ofReal
        (2 * Real.exp
          (-eps ^ 2 / (2 * (((Finset.range n).sum cY : NNReal) : Real)))) := by
  let S : Omega -> Real := fun omega =>
    (Finset.range n).sum (fun i => Y i omega)
  let variance : NNReal := (Finset.range n).sum cY
  let tailReal : Real :=
    Real.exp (-eps ^ 2 / (2 * ((variance : NNReal) : Real)))
  have htail_nonneg : 0 <= tailReal := (Real.exp_pos _).le
  have hsum : ProbabilityTheory.HasSubgaussianMGF S variance mu := by
    simpa [S, variance] using
      (ProbabilityTheory.HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
        h_adapted h0 n h_subG)
  have hupperReal :
      mu.real {omega | eps <= S omega} <= tailReal := by
    simpa [tailReal] using hsum.measure_ge_le heps
  have hupper :
      mu {omega | eps <= S omega} <= ENNReal.ofReal tailReal := by
    rw [Measure.real] at hupperReal
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top mu {omega | eps <= S omega}) htail_nonneg).2
      hupperReal
  have hlowerReal :
      mu.real {omega | eps <= (-S) omega} <= tailReal := by
    simpa [tailReal] using hsum.neg.measure_ge_le heps
  have hlower :
      mu {omega | eps <= (-S) omega} <= ENNReal.ofReal tailReal := by
    rw [Measure.real] at hlowerReal
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top mu {omega | eps <= (-S) omega}) htail_nonneg).2
      hlowerReal
  have hsubset :
      {omega | eps <= |S omega|} ⊆
        {omega | eps <= S omega} ∪ {omega | eps <= (-S) omega} := by
    intro omega homega
    by_cases hnonneg : 0 <= S omega
    · exact Or.inl (by simpa [abs_of_nonneg hnonneg] using homega)
    · have hnonpos : S omega <= 0 := le_of_not_ge hnonneg
      exact Or.inr (by simpa [abs_of_nonpos hnonpos] using homega)
  calc
    mu {omega |
        eps <= |(Finset.range n).sum (fun i => Y i omega)|}
        = mu {omega | eps <= |S omega|} := by rfl
    _ <= mu ({omega | eps <= S omega} ∪
        {omega | eps <= (-S) omega}) := measure_mono hsubset
    _ <= mu {omega | eps <= S omega} +
        mu {omega | eps <= (-S) omega} := measure_union_le _ _
    _ <= ENNReal.ofReal tailReal + ENNReal.ofReal tailReal :=
      add_le_add hupper hlower
    _ = ENNReal.ofReal
        (2 * Real.exp
          (-eps ^ 2 / (2 * (((Finset.range n).sum cY : NNReal) : Real)))) := by
      rw [← ENNReal.ofReal_add htail_nonneg htail_nonneg]
      simp [tailReal, variance, two_mul]

/--
Two-sided fixed-horizon sub-Gaussian confidence radius for total proxy
variance `variance` and failure budget `delta`.
-/
noncomputable def subGaussianSumConfidenceRadius
    (variance : NNReal) (delta : Real) : Real :=
  Real.sqrt (2 * ((variance : NNReal) : Real) * Real.log (2 / delta))

theorem subGaussianSumConfidenceRadius_nonneg
    (variance : NNReal) (delta : Real) :
    0 <= subGaussianSumConfidenceRadius variance delta := by
  exact Real.sqrt_nonneg _

theorem subGaussianSumConfidenceRadius_sq
    (variance : NNReal) (delta : Real)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (subGaussianSumConfidenceRadius variance delta) ^ 2 =
      2 * ((variance : NNReal) : Real) * Real.log (2 / delta) := by
  have hscale : 1 <= 2 / delta := by
    rw [le_div_iff₀ hdelta]
    linarith
  have hlog : 0 <= Real.log (2 / delta) := Real.log_nonneg hscale
  rw [subGaussianSumConfidenceRadius, Real.sq_sqrt]
  positivity

theorem two_mul_exp_neg_subGaussianSumConfidenceRadius_sq_div_eq_delta
    (variance : NNReal) (delta : Real)
    (hvariance : 0 < ((variance : NNReal) : Real))
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    2 * Real.exp
        (-(subGaussianSumConfidenceRadius variance delta) ^ 2 /
          (2 * ((variance : NNReal) : Real))) =
      delta := by
  rw [subGaussianSumConfidenceRadius_sq variance delta hdelta hdelta_le_one]
  have hden : Ne (2 * ((variance : NNReal) : Real)) 0 := by positivity
  have hexponent :
      -(2 * ((variance : NNReal) : Real) * Real.log (2 / delta)) /
          (2 * ((variance : NNReal) : Real)) =
        -Real.log (2 / delta) := by
    field_simp [hden]
  rw [hexponent, Real.exp_neg]
  have hscale : 0 < 2 / delta := by positivity
  rw [Real.exp_log hscale]
  field_simp

/--
Delta-calibrated two-sided confidence bound for a finite sum of independent
sub-Gaussian random variables.
-/
theorem subGaussian_sum_abs_tail_ennreal_delta_of_iIndepFun
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {Idx : Type v} {X : Idx -> Omega -> Real}
    (h_indep : ProbabilityTheory.iIndepFun X mu)
    {c : Idx -> NNReal} {s : Finset Idx}
    (h_subG :
      forall i, i ∈ s ->
        ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu)
    (hvariance : 0 < (((s.sum c : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    mu {omega |
        subGaussianSumConfidenceRadius (s.sum c) delta <=
          |s.sum (fun i => X i omega)|} <=
      ENNReal.ofReal delta := by
  have htail :=
    subGaussian_sum_abs_tail_ennreal_of_iIndepFun
      mu h_indep h_subG
      (subGaussianSumConfidenceRadius_nonneg (s.sum c) delta)
  rw [two_mul_exp_neg_subGaussianSumConfidenceRadius_sq_div_eq_delta
    (s.sum c) delta hvariance hdelta hdelta_le_one] at htail
  exact htail

/--
Delta-calibrated two-sided Azuma-Hoeffding confidence bound for a finite prefix
of a strongly adapted conditionally sub-Gaussian process.

The positive-total-variance contract is required because the bad event is
written with non-strict `radius <= |sum|`; at zero variance the zero-radius
event contains the almost-sure equality path.
-/
theorem condSubGaussian_sum_abs_tail_ennreal_delta_of_stronglyAdapted
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] [IsZeroOrProbabilityMeasure mu]
    {Y : Nat -> Omega -> Real} {cY : Nat -> NNReal}
    {F : Filtration Nat mOmega}
    (h_adapted : StronglyAdapted F Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu)
    (n : Nat)
    (h_subG :
      forall i, i < n - 1 ->
        ProbabilityTheory.HasCondSubgaussianMGF
          (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu)
    (hvariance :
      0 < ((((Finset.range n).sum cY : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    mu {omega |
        subGaussianSumConfidenceRadius
            ((Finset.range n).sum cY) delta <=
          |(Finset.range n).sum (fun i => Y i omega)|} <=
      ENNReal.ofReal delta := by
  have htail :=
    condSubGaussian_sum_abs_tail_ennreal_of_stronglyAdapted
      h_adapted h0 n h_subG
      (subGaussianSumConfidenceRadius_nonneg
        ((Finset.range n).sum cY) delta)
  rw [two_mul_exp_neg_subGaussianSumConfidenceRadius_sq_div_eq_delta
    ((Finset.range n).sum cY) delta hvariance hdelta hdelta_le_one] at htail
  exact htail

/--
Two-sided confidence radius for the average of `samples` centered increments.
The total proxy variance belongs to the corresponding sum and the division by
`samples` performs only the deterministic sum-to-average conversion.
-/
noncomputable def subGaussianAverageConfidenceRadius
    (variance : NNReal) (samples : Nat) (delta : Real) : Real :=
  subGaussianSumConfidenceRadius variance delta / (samples : Real)

theorem subGaussianAverageConfidenceRadius_nonneg
    (variance : NNReal) (samples : Nat) (delta : Real) :
    0 <= subGaussianAverageConfidenceRadius variance samples delta := by
  exact div_nonneg
    (subGaussianSumConfidenceRadius_nonneg variance delta)
    (Nat.cast_nonneg samples)

/--
Deterministic positive-sample-count transport from a two-sided sum-confidence
bound to the corresponding average-confidence bound.
-/
theorem measure_average_abs_tail_le_of_measure_sum_abs_tail
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) (X : Omega -> Real)
    (variance : NNReal) (m : Nat) (hm : 0 < m) (delta : Real)
    (htail :
      mu {omega |
          subGaussianSumConfidenceRadius variance delta <= |X omega|} <=
        ENNReal.ofReal delta) :
    mu {omega |
        subGaussianAverageConfidenceRadius variance m delta <=
          |X omega / (m : Real)|} <=
      ENNReal.ofReal delta := by
  have hmReal : 0 < (m : Real) := by exact_mod_cast hm
  refine (measure_mono ?_).trans htail
  intro omega homega
  change
    subGaussianAverageConfidenceRadius variance m delta <=
      |X omega / (m : Real)| at homega
  change subGaussianSumConfidenceRadius variance delta <= |X omega|
  have habsDiv : |X omega / (m : Real)| = |X omega| / (m : Real) := by
    rw [abs_div, abs_of_pos hmReal]
  rw [subGaussianAverageConfidenceRadius, habsDiv] at homega
  exact (div_le_div_iff_of_pos_right hmReal).mp homega

/--
Positive random-count transport from a two-sided sum-confidence bound to the
corresponding average-confidence bound.

No measurability of `count` is needed: Mathlib measures are outer measures on
arbitrary sets, and the proof is the pointwise inclusion obtained by
multiplying through by the positive realized count.
-/
theorem measure_randomCount_average_abs_tail_le_of_measure_sum_abs_tail
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) (X : Omega -> Real) (count : Omega -> Nat)
    (variance : NNReal) (delta : Real)
    (htail :
      mu {omega |
          subGaussianSumConfidenceRadius variance delta <= |X omega|} <=
        ENNReal.ofReal delta) :
    mu {omega |
        0 < count omega ∧
          subGaussianAverageConfidenceRadius variance (count omega) delta <=
            |X omega / (count omega : Real)|} <=
      ENNReal.ofReal delta := by
  refine (measure_mono ?_).trans htail
  intro omega homega
  rcases homega with ⟨hcount, homega⟩
  have hcountReal : 0 < (count omega : Real) := by exact_mod_cast hcount
  have habsDiv :
      |X omega / (count omega : Real)| =
        |X omega| / (count omega : Real) := by
    rw [abs_div, abs_of_pos hcountReal]
  rw [subGaussianAverageConfidenceRadius, habsDiv] at homega
  exact (div_le_div_iff_of_pos_right hcountReal).mp homega

/-- A positive random-count event is covered by its exact-count fibers up to a
deterministic count ceiling. This is an outer-measure statement, so neither the
count nor the fiber events need to be measurable. -/
theorem measure_positive_randomCount_event_le_sum_exactCount
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) (count : Omega -> Nat) (maxCount : Nat)
    (bad : Nat -> Set Omega)
    (hcount_le : forall omega, count omega <= maxCount) :
    mu {omega | 0 < count omega ∧ omega ∈ bad (count omega)} <=
      (Finset.range maxCount).sum (fun i =>
        mu {omega | count omega = i + 1 ∧ omega ∈ bad (i + 1)}) := by
  have hsubset :
      {omega | 0 < count omega ∧ omega ∈ bad (count omega)} ⊆
        ⋃ i ∈ Finset.range maxCount,
          {omega | count omega = i + 1 ∧ omega ∈ bad (i + 1)} := by
    intro omega homega
    rcases homega with ⟨hcount_pos, hbad⟩
    let i := count omega - 1
    have hcount_bound := hcount_le omega
    have hi_lt : i < maxCount := by
      dsimp [i]
      omega
    have hi_succ : i + 1 = count omega := by
      dsimp [i]
      omega
    simp only [Set.mem_iUnion]
    refine ⟨i, ⟨Finset.mem_range.mpr hi_lt, ?_⟩⟩
    exact ⟨hi_succ.symm, by simpa [hi_succ] using hbad⟩
  calc
    mu {omega | 0 < count omega ∧ omega ∈ bad (count omega)} <=
        mu (⋃ i ∈ Finset.range maxCount,
          {omega | count omega = i + 1 ∧ omega ∈ bad (i + 1)}) :=
      measure_mono hsubset
    _ <= (Finset.range maxCount).sum (fun i =>
        mu {omega | count omega = i + 1 ∧ omega ∈ bad (i + 1)}) :=
      ProbabilityUnionBound.measure_biUnion_finset_le
        mu (Finset.range maxCount) fun i =>
          {omega | count omega = i + 1 ∧ omega ∈ bad (i + 1)}

/-- Equal-share finite peeling over every positive exact-count fiber. -/
theorem measure_positive_randomCount_event_le_of_exactCount_uniform
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) (count : Omega -> Nat) (maxCount : Nat)
    (bad : Nat -> Set Omega)
    (hcount_le : forall omega, count omega <= maxCount)
    (hmaxCount : 0 < maxCount)
    (delta : Real) (_hdelta : 0 < delta)
    (hfiber : forall k, 0 < k -> k <= maxCount ->
      mu {omega | count omega = k ∧ omega ∈ bad k} <=
        ENNReal.ofReal (delta / (maxCount : Real))) :
    mu {omega | 0 < count omega ∧ omega ∈ bad (count omega)} <=
      ENNReal.ofReal delta := by
  have hmaxReal : 0 < (maxCount : Real) := Nat.cast_pos.mpr hmaxCount
  have hmaxENN_ne_zero : (maxCount : ENNReal) ≠ 0 := by
    simpa using hmaxCount.ne'
  have hmaxENN_ne_top : (maxCount : ENNReal) ≠ ⊤ := by simp
  calc
    mu {omega | 0 < count omega ∧ omega ∈ bad (count omega)} <=
        (Finset.range maxCount).sum (fun i =>
          mu {omega | count omega = i + 1 ∧ omega ∈ bad (i + 1)}) :=
      measure_positive_randomCount_event_le_sum_exactCount
        mu count maxCount bad hcount_le
    _ <= (Finset.range maxCount).sum (fun _ =>
        ENNReal.ofReal (delta / (maxCount : Real))) := by
      exact Finset.sum_le_sum fun i hi =>
        hfiber (i + 1) (Nat.succ_pos i)
          (Nat.succ_le_iff.mpr (Finset.mem_range.mp hi))
    _ = (maxCount : ENNReal) *
        ENNReal.ofReal (delta / (maxCount : Real)) := by
      simp [nsmul_eq_mul]
    _ = ENNReal.ofReal delta := by
      rw [ENNReal.ofReal_div_of_pos hmaxReal]
      simp only [ENNReal.ofReal_natCast]
      exact ENNReal.mul_div_cancel hmaxENN_ne_zero hmaxENN_ne_top

/--
Delta-calibrated two-sided confidence bound for the average of exactly `m`
independent sub-Gaussian random variables indexed by a finite set.
-/
theorem subGaussian_average_abs_tail_ennreal_delta_of_iIndepFun
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {X : Nat -> Omega -> Real} {c : Nat -> NNReal}
    (h_indep : ProbabilityTheory.iIndepFun X mu)
    (m : Nat) (hm : 0 < m)
    (h_subG :
      forall i, i < m ->
        ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu)
    (hvariance :
      0 < ((((Finset.range m).sum c : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    mu {omega |
        subGaussianAverageConfidenceRadius
            ((Finset.range m).sum c) m delta <=
          |((Finset.range m).sum (fun i => X i omega)) / (m : Real)|} <=
      ENNReal.ofReal delta := by
  have htail :=
    subGaussian_sum_abs_tail_ennreal_delta_of_iIndepFun
      mu h_indep (s := Finset.range m)
      (fun i hi => h_subG i (Finset.mem_range.mp hi))
      hvariance delta hdelta hdelta_le_one
  exact
    measure_average_abs_tail_le_of_measure_sum_abs_tail
      mu (fun omega => (Finset.range m).sum (fun i => X i omega))
      ((Finset.range m).sum c) m hm delta htail

/--
Delta-calibrated two-sided confidence bound for the average of exactly `m`
successor increments in a zero-initialized conditional sub-Gaussian process.

The process prefix is `Finset.range (m + 1)`: slot zero is the deterministic
initial value and slots `1, ..., m` are the `m` averaged increments.  The proof
is a positive-denominator event transport from the compiled sum confidence
theorem.
-/
theorem condSubGaussian_average_abs_tail_ennreal_delta_of_stronglyAdapted
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] [IsZeroOrProbabilityMeasure mu]
    {Y : Nat -> Omega -> Real} {cY : Nat -> NNReal}
    {F : Filtration Nat mOmega}
    (h_adapted : StronglyAdapted F Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu)
    (m : Nat) (hm : 0 < m)
    (h_subG :
      forall i, i < (m + 1) - 1 ->
        ProbabilityTheory.HasCondSubgaussianMGF
          (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu)
    (hvariance :
      0 < ((((Finset.range (m + 1)).sum cY : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    mu {omega |
        subGaussianAverageConfidenceRadius
            ((Finset.range (m + 1)).sum cY) m delta <=
          |((Finset.range (m + 1)).sum (fun i => Y i omega)) /
            (m : Real)|} <=
      ENNReal.ofReal delta := by
  have htail :=
    condSubGaussian_sum_abs_tail_ennreal_delta_of_stronglyAdapted
      h_adapted h0 (m + 1) h_subG hvariance delta hdelta hdelta_le_one
  exact
    measure_average_abs_tail_le_of_measure_sum_abs_tail
      mu (fun omega =>
        (Finset.range (m + 1)).sum (fun i => Y i omega))
      ((Finset.range (m + 1)).sum cY) m hm delta htail

/--
Fixed-tilt one-sided tail for a conditionally sub-Gaussian process masked by
conditioning-measurable events.  The event retains the random cumulative
masked proxy instead of charging every time step.
-/
theorem condSubGaussian_indicator_sum_tail_predictableVariance_fixedTilt
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (F : Filtration Nat mOmega)
    (X : Nat -> Omega -> Real) (c : Nat -> NNReal)
    (s : Nat -> Set Omega)
    (hY : StronglyAdapted F (fun t omega =>
      match t with
      | 0 => 0
      | i + 1 => (s i).indicator (X i) omega))
    (hV : StronglyAdapted F (fun t omega =>
      match t with
      | 0 => 0
      | i + 1 =>
          (s i).indicator (fun _ => (((c i : NNReal) : Real))) omega))
    (hs : forall i, @MeasurableSet Omega (F i) (s i))
    (n : Nat)
    (h_subG : forall i, i < n - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (X i) (c i) mu)
    (tilt : Real) (htilt : 0 <= tilt)
    (threshold varianceBudget : Real) :
    mu {omega |
        threshold <= (Finset.range n).sum (fun t =>
          match t with
          | 0 => 0
          | i + 1 => (s i).indicator (X i) omega) ∧
        (Finset.range n).sum (fun t =>
          match t with
          | 0 => 0
          | i + 1 =>
              (s i).indicator
                (fun _ => (((c i : NNReal) : Real))) omega) <=
          varianceBudget} <=
      ENNReal.ofReal (Real.exp
        (-tilt * threshold + (tilt ^ 2 / 2) * varianceBudget)) := by
  let Y : Nat -> Omega -> Real := fun t omega =>
    match t with
    | 0 => 0
    | i + 1 => (s i).indicator (X i) omega
  let V : Nat -> Omega -> Real := fun t omega =>
    match t with
    | 0 => 0
    | i + 1 =>
        (s i).indicator (fun _ => (((c i : NNReal) : Real))) omega
  let Z : Nat -> Omega -> Real := fun t omega =>
    tilt * Y t omega - (tilt ^ 2 / 2) * V t omega
  have hZ : StronglyAdapted F Z := by
    intro i
    exact ((hY i).const_mul tilt).sub ((hV i).const_mul (tilt ^ 2 / 2))
  have hzero : HasMGFUpperBoundAt (Z 0) 1 0 mu := by
    have hzero' : HasMGFUpperBoundAt (fun _ : Omega => (0 : Real)) 1 0 mu := by
      constructor
      · intro a
        simp
      · simp [ProbabilityTheory.mgf]
    simpa [Z, Y, V] using hzero'
  have hcond : forall i, i < n - 1 ->
      HasCondMGFUpperBoundAt (F i) (F.le i) (Z (i + 1)) 1 0 mu := by
    intro i hi
    have h :=
      (h_subG i hi).indicator_compensated_hasCondMGFUpperBoundAt
        (F.le i) (hs i) tilt
    convert h using 1
    funext omega
    by_cases homega : omega ∈ s i
    · simp [Z, Y, V, homega]
      ring
    · simp [Z, Y, V, homega]
  have htail :=
    measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt
      (μ := mu) (ℱ := F) Y V n tilt (tilt ^ 2 / 2)
        threshold varianceBudget
        (by simpa [Y, V, Z] using hZ)
        (by simpa [Y, V, Z] using hzero)
        (by simpa [Y, V, Z] using hcond)
        htilt (by positivity)
  simpa [Y, V, mul_assoc] using htail

/-- Delta radius for a two-sided masked conditionally sub-Gaussian sum under
a deterministic budget on its random cumulative predictable proxy. -/
noncomputable def subGaussianPredictableVarianceRadius
    (varianceBudget delta : Real) : Real :=
  quadraticFixedMGFRadius (1 / 2) varianceBudget 1 (delta / 2)

/--
Two-sided delta tail for a conditionally sub-Gaussian process with a
conditioning-measurable mask and a random cumulative predictable proxy.
-/
theorem condSubGaussian_indicator_sum_abs_tail_predictableVariance_delta
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (F : Filtration Nat mOmega)
    (X : Nat -> Omega -> Real) (c : Nat -> NNReal)
    (s : Nat -> Set Omega)
    (hY : StronglyAdapted F (fun t omega =>
      match t with
      | 0 => 0
      | i + 1 => (s i).indicator (X i) omega))
    (hV : StronglyAdapted F (fun t omega =>
      match t with
      | 0 => 0
      | i + 1 =>
          (s i).indicator (fun _ => (((c i : NNReal) : Real))) omega))
    (hs : forall i, @MeasurableSet Omega (F i) (s i))
    (n : Nat)
    (h_subG : forall i, i < n - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (X i) (c i) mu)
    (varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta) :
    mu {omega |
        subGaussianPredictableVarianceRadius varianceBudget delta <=
          |(Finset.range n).sum (fun t =>
            match t with
            | 0 => 0
            | i + 1 => (s i).indicator (X i) omega)| ∧
        (Finset.range n).sum (fun t =>
          match t with
          | 0 => 0
          | i + 1 =>
              (s i).indicator
                (fun _ => (((c i : NNReal) : Real))) omega) <=
          varianceBudget} <=
      ENNReal.ofReal delta := by
  let Y : Nat -> Omega -> Real := fun t omega =>
    match t with
    | 0 => 0
    | i + 1 => (s i).indicator (X i) omega
  let V : Nat -> Omega -> Real := fun t omega =>
    match t with
    | 0 => 0
    | i + 1 =>
        (s i).indicator (fun _ => (((c i : NNReal) : Real))) omega
  let radius := subGaussianPredictableVarianceRadius varianceBudget delta
  have hhalf : 0 < delta / 2 := by positivity
  have hupper :
      mu {omega | radius <= (Finset.range n).sum (fun t => Y t omega) ∧
          (Finset.range n).sum (fun t => V t omega) <= varianceBudget} <=
        ENNReal.ofReal (delta / 2) := by
    have htail :=
      measure_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail
        mu
        (fun omega => (Finset.range n).sum (fun t => Y t omega))
        (fun omega => (Finset.range n).sum (fun t => V t omega))
        (1 / 2) varianceBudget 1 (delta / 2)
        (by norm_num) hvarianceBudget (by norm_num) hhalf (by
          intro tilt htilt htilt_le
          have hfixed :=
            (condSubGaussian_indicator_sum_tail_predictableVariance_fixedTilt
              F X c s hY hV hs n h_subG tilt htilt
                (quadraticFixedMGFRadius
                  (1 / 2) varianceBudget 1 (delta / 2)) varianceBudget)
          have hexponent :
              -tilt * quadraticFixedMGFRadius
                    (1 / 2) varianceBudget 1 (delta / 2) +
                  (1 / 2) * (tilt ^ 2 * varianceBudget) =
                -tilt * quadraticFixedMGFRadius
                    (1 / 2) varianceBudget 1 (delta / 2) +
                  (tilt ^ 2 / 2) * varianceBudget := by ring
          rw [hexponent]
          simpa [Y, V] using hfixed)
    simpa [radius, subGaussianPredictableVarianceRadius, Y, V] using htail
  let Xneg : Nat -> Omega -> Real := fun i omega => -X i omega
  let Yneg : Nat -> Omega -> Real := fun t omega =>
    match t with
    | 0 => 0
    | i + 1 => (s i).indicator (Xneg i) omega
  have hYneg : StronglyAdapted F Yneg := by
    intro i
    cases i with
    | zero => exact stronglyMeasurable_const
    | succ i =>
        simpa [Yneg, Y, Xneg, Set.indicator_neg] using (hY (i + 1)).neg
  have h_subG_neg : forall i, i < n - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (Xneg i) (c i) mu := by
    intro i hi
    simpa [Xneg] using (h_subG i hi).neg
  have hlower :
      mu {omega | radius <= -(Finset.range n).sum (fun t => Y t omega) ∧
          (Finset.range n).sum (fun t => V t omega) <= varianceBudget} <=
        ENNReal.ofReal (delta / 2) := by
    have htail :=
      measure_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail
        mu
        (fun omega => (Finset.range n).sum (fun t => Yneg t omega))
        (fun omega => (Finset.range n).sum (fun t => V t omega))
        (1 / 2) varianceBudget 1 (delta / 2)
        (by norm_num) hvarianceBudget (by norm_num) hhalf (by
          intro tilt htilt htilt_le
          have hfixed :=
            (condSubGaussian_indicator_sum_tail_predictableVariance_fixedTilt
              F Xneg c s hYneg hV hs n h_subG_neg tilt htilt
                (quadraticFixedMGFRadius
                  (1 / 2) varianceBudget 1 (delta / 2)) varianceBudget)
          have hexponent :
              -tilt * quadraticFixedMGFRadius
                    (1 / 2) varianceBudget 1 (delta / 2) +
                  (1 / 2) * (tilt ^ 2 * varianceBudget) =
                -tilt * quadraticFixedMGFRadius
                    (1 / 2) varianceBudget 1 (delta / 2) +
                  (tilt ^ 2 / 2) * varianceBudget := by ring
          rw [hexponent]
          simpa [Yneg, V] using hfixed)
    have hsum_neg : forall omega,
        (Finset.range n).sum (fun t => Yneg t omega) =
          -(Finset.range n).sum (fun t => Y t omega) := by
      intro omega
      calc
        (Finset.range n).sum (fun t => Yneg t omega) =
            (Finset.range n).sum (fun t => -Y t omega) := by
              apply Finset.sum_congr rfl
              intro t _ht
              cases t <;> simp [Yneg, Y, Xneg, Set.indicator_neg]
        _ = -(Finset.range n).sum (fun t => Y t omega) := by
          rw [Finset.sum_neg_distrib]
    change
      mu {omega |
          subGaussianPredictableVarianceRadius varianceBudget delta <=
              -(Finset.range n).sum (fun t => Y t omega) ∧
            (Finset.range n).sum (fun t => V t omega) <= varianceBudget} <=
        ENNReal.ofReal (delta / 2)
    simpa [subGaussianPredictableVarianceRadius, hsum_neg] using htail
  have hsubset :
      {omega | radius <= |(Finset.range n).sum (fun t => Y t omega)| ∧
          (Finset.range n).sum (fun t => V t omega) <= varianceBudget} ⊆
        {omega | radius <= (Finset.range n).sum (fun t => Y t omega) ∧
          (Finset.range n).sum (fun t => V t omega) <= varianceBudget} ∪
        {omega | radius <= -(Finset.range n).sum (fun t => Y t omega) ∧
          (Finset.range n).sum (fun t => V t omega) <= varianceBudget} := by
    intro omega homega
    by_cases hnonneg : 0 <= (Finset.range n).sum (fun t => Y t omega)
    · exact Or.inl ⟨by simpa [abs_of_nonneg hnonneg] using homega.1,
        homega.2⟩
    · have hnonpos : (Finset.range n).sum (fun t => Y t omega) <= 0 :=
        le_of_not_ge hnonneg
      exact Or.inr ⟨by simpa [abs_of_nonpos hnonpos] using homega.1,
        homega.2⟩
  calc
    mu {omega |
        subGaussianPredictableVarianceRadius varianceBudget delta <=
          |(Finset.range n).sum (fun t =>
            match t with
            | 0 => 0
            | i + 1 => (s i).indicator (X i) omega)| ∧
        (Finset.range n).sum (fun t =>
          match t with
          | 0 => 0
          | i + 1 =>
              (s i).indicator
                (fun _ => (((c i : NNReal) : Real))) omega) <=
          varianceBudget} =
        mu {omega | radius <= |(Finset.range n).sum (fun t => Y t omega)| ∧
          (Finset.range n).sum (fun t => V t omega) <= varianceBudget} := by
            rfl
    _ <= mu
        ({omega | radius <= (Finset.range n).sum (fun t => Y t omega) ∧
          (Finset.range n).sum (fun t => V t omega) <= varianceBudget} ∪
        {omega | radius <= -(Finset.range n).sum (fun t => Y t omega) ∧
          (Finset.range n).sum (fun t => V t omega) <= varianceBudget}) :=
      measure_mono hsubset
    _ <= mu {omega | radius <= (Finset.range n).sum (fun t => Y t omega) ∧
          (Finset.range n).sum (fun t => V t omega) <= varianceBudget} +
        mu {omega | radius <= -(Finset.range n).sum (fun t => Y t omega) ∧
          (Finset.range n).sum (fun t => V t omega) <= varianceBudget} :=
      measure_union_le _ _
    _ <= ENNReal.ofReal (delta / 2) + ENNReal.ofReal (delta / 2) :=
      add_le_add hupper hlower
    _ = ENNReal.ofReal delta := by
      rw [← ENNReal.ofReal_add hhalf.le hhalf.le]
      congr 1
      ring

end Concentration
end BanditRLProof
