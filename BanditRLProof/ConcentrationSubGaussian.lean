import Mathlib.Probability.Moments.SubGaussian

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

end Concentration
end BanditRLProof
