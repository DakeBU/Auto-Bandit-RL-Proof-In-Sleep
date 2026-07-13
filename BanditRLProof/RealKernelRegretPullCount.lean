import Mathlib.Probability.Kernel.Integral
import BanditRLProof.RealMeanRegretPullCount

/-!
# Real kernel regret and pull-count decomposition

This module specializes the Real mean-regret bookkeeping surface to an
arm-indexed Mathlib kernel.  The mean of arm `a` is the Bochner integral of the
identity under the measure `nu a`, exactly as in the LML finite-bandit regret
definitions.  Algorithm laws and concentration assumptions remain downstream.
-/

namespace BanditRLProof

open MeasureTheory

universe u

/-- Identity-integral mean of a Real-valued arm kernel. -/
noncomputable def realKernelMean {K : Nat}
    (nu : ProbabilityTheory.Kernel (Fin K) Real) (a : Fin K) : Real :=
  integral (nu a) id

/-- Gap of a Real-valued arm kernel from its supremum arm mean. -/
noncomputable def realKernelGap {K : Nat}
    (nu : ProbabilityTheory.Kernel (Fin K) Real) (a : Fin K) : Real :=
  realMeanGap (realKernelMean nu) a

/-- Finite-horizon regret of an action trace against a Real-valued arm kernel. -/
noncomputable def realKernelRegret {K : Nat}
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    (action : ActionTrace (Fin K)) (n : Nat) : Real :=
  realMeanRegret (realKernelMean nu) action n

/-- Every kernel arm gap is nonnegative when the finite arm type is nonempty. -/
theorem realKernelGap_nonneg
    {K : Nat} [Nonempty (Fin K)]
    (nu : ProbabilityTheory.Kernel (Fin K) Real) (a : Fin K) :
    0 <= realKernelGap nu a := by
  rw [realKernelGap, realMeanGap, sub_nonneg]
  exact le_ciSup (f := realKernelMean nu) (by simp) a

/-- Kernel regret is the finite time-indexed sum of selected kernel gaps. -/
theorem realKernelRegret_eq_finset_sum_gap
    {K : Nat}
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    (action : ActionTrace (Fin K)) (n : Nat) :
    realKernelRegret nu action n =
      (Finset.range n).sum (fun t => realKernelGap nu (action t)) := by
  simpa [realKernelRegret, realKernelGap] using
    realMeanRegret_eq_finset_sum_gap (realKernelMean nu) action n

/-- Kernel regret is the gap-weighted finite sum of arm pull counts. -/
theorem realKernelRegret_eq_sum_gap_mul_pullCount
    {K : Nat}
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    (action : ActionTrace (Fin K)) (n : Nat) :
    realKernelRegret nu action n =
      (Finset.univ : Finset (Fin K)).sum
        (fun a => realKernelGap nu a * (pullCount action a n : Real)) := by
  simpa [realKernelRegret, realKernelGap] using
    realMeanRegret_eq_sum_gap_mul_pullCount (realKernelMean nu) action n

/-- Pull-count integrability implies integrability of Real kernel regret. -/
theorem integrable_realKernelRegret_of_integrable_pullCount
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    (action : Omega -> ActionTrace (Fin K))
    (n : Nat)
    (hcount : forall a : Fin K,
      Integrable (fun omega => (pullCount (action omega) a n : Real)) mu) :
    Integrable (fun omega => realKernelRegret nu (action omega) n) mu := by
  simpa [realKernelRegret] using
    integrable_realMeanRegret_of_integrable_pullCount
      mu (realKernelMean nu) action n hcount

/--
The Bochner expectation of Real kernel regret is the gap-weighted sum of
expected arm pull counts.

This is the kernel-facing bookkeeping endpoint for the exact ETC route.  It
does not assume a Markov kernel, probability measure, identity integrability,
algorithm/environment law, sub-Gaussian proxy, or argmax semantics.  Those
contracts are required only by downstream statistical theorems.
-/
theorem integral_realKernelRegret_eq_sum_gap_mul_integral_pullCount
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    (action : Omega -> ActionTrace (Fin K))
    (n : Nat)
    (hcount : forall a : Fin K,
      Integrable (fun omega => (pullCount (action omega) a n : Real)) mu) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) =
      (Finset.univ : Finset (Fin K)).sum
        (fun a =>
          realKernelGap nu a *
            integral mu (fun omega => (pullCount (action omega) a n : Real))) := by
  simpa [realKernelRegret, realKernelGap] using
    integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount
      mu (realKernelMean nu) action n hcount

end BanditRLProof
