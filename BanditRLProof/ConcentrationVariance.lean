import Mathlib.Probability.Moments.Variance

/-!
# Variance concentration wrappers

This module exposes small Mathlib-backed variance/Chebyshev imports under the
project namespace.  It is only the reusable finite-variance tail layer: no
robust mean estimator, bandit reward law, or final regret theorem is introduced
here.
-/

namespace BanditRLProof
namespace Concentration

open MeasureTheory
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

/--
Mathlib-backed Chebyshev tail bound for a real random variable with finite
second moment.

This is the real-variance `TAIL-VARIANCE-ROBUST` import wrapper.  It keeps the
Mathlib contract explicit: a finite measure, a real variable in `L^2`, and a
strictly positive deviation radius.
-/
theorem variance_chebyshev_tail
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {X : Omega -> Real}
    (hX : MemLp X 2 mu)
    {eps : Real} (heps : 0 < eps) :
    mu {omega | eps <= |X omega - integral mu X|} <=
      ENNReal.ofReal (ProbabilityTheory.variance X mu / eps ^ 2) := by
  exact ProbabilityTheory.meas_ge_le_variance_div_sq hX heps

/--
Extended-real Chebyshev tail bound using Mathlib's `evariance` formulation.

This version only requires almost-everywhere strong measurability; if the
extended variance is infinite the bound is correspondingly non-informative.
-/
theorem evariance_chebyshev_tail
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega)
    {X : Omega -> Real}
    (hX : AEStronglyMeasurable X mu)
    {eps : NNReal} (heps : Ne eps 0) :
    mu {omega | (eps : Real) <= |X omega - integral mu X|} <=
      ProbabilityTheory.evariance X mu / (eps : ENNReal) ^ 2 := by
  exact ProbabilityTheory.meas_ge_le_evariance_div_sq hX heps

/--
Mathlib-backed variance additivity for a finite sum of pairwise independent
real random variables.

This is a bookkeeping wrapper used by finite-variance routes before a
bandit-specific empirical-mean specialization exists.
-/
theorem variance_sum_of_pairwise_indep
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {Idx : Type v} {X : Idx -> Omega -> Real} {s : Finset Idx}
    (h_mem : forall i : Idx, Membership.mem s i -> MemLp (X i) 2 mu)
    (h_pairwise :
      Set.Pairwise ((s : Finset Idx) : Set Idx)
        (fun i j => ProbabilityTheory.IndepFun (X i) (X j) mu)) :
    ProbabilityTheory.variance (Finset.sum s X) mu =
      Finset.sum s (fun i => ProbabilityTheory.variance (X i) mu) := by
  exact ProbabilityTheory.IndepFun.variance_sum h_mem h_pairwise

end Concentration
end BanditRLProof
