import Mathlib.MeasureTheory.Integral.Bochner.Basic
import BanditRLProof.ExpectationBochnerSums
import BanditRLProof.IntegrabilitySums
import BanditRLProof.MathlibWrappers

/-!
# Real mean-regret pull-count decomposition

This module provides the Real-valued finite-arm bookkeeping surface needed by
the exact LML ETC route.  It is parameterized by an arm-mean function, so a
later kernel bridge can instantiate `mean a` with the integral of the identity
under arm `a` without changing the deterministic or Bochner proofs here.
-/

namespace BanditRLProof

open MeasureTheory

universe u

/-- Gap from the supremum finite-arm mean, matching the scalar semantics of LML's bandit gap. -/
noncomputable def realMeanGap {K : Nat} (mean : Fin K -> Real) (a : Fin K) : Real :=
  (⨆ b : Fin K, mean b) - mean a

/-- Real pseudo-regret written directly from arm means over a finite horizon. -/
noncomputable def realMeanRegret {K : Nat}
    (mean : Fin K -> Real) (action : ActionTrace (Fin K)) (n : Nat) : Real :=
  (n : Real) * (⨆ a : Fin K, mean a) -
    (Finset.range n).sum (fun t => mean (action t))

/-- Real mean regret is the time-indexed finite sum of selected arm gaps. -/
theorem realMeanRegret_eq_finset_sum_gap
    {K : Nat}
    (mean : Fin K -> Real)
    (action : ActionTrace (Fin K))
    (n : Nat) :
    realMeanRegret mean action n =
      (Finset.range n).sum (fun t => realMeanGap mean (action t)) := by
  simp [realMeanRegret, realMeanGap, Finset.sum_sub_distrib]

/--
Real mean regret decomposes into each arm gap times its finite-horizon pull count.

This is the deterministic half of `REAL-MEAN-REGRET-PULLCOUNT`.  The definition
uses the same supremum-minus-mean gap as the exact LML theorem card; no rational
model, kernel law, measurability, or concentration assumption appears here.
-/
theorem realMeanRegret_eq_sum_gap_mul_pullCount
    {K : Nat}
    (mean : Fin K -> Real)
    (action : ActionTrace (Fin K))
    (n : Nat) :
    realMeanRegret mean action n =
      (Finset.univ : Finset (Fin K)).sum
        (fun a => realMeanGap mean a * (pullCount action a n : Real)) := by
  rw [realMeanRegret_eq_finset_sum_gap]
  rw [(Finset.sum_fiberwise'
    (s := Finset.range n)
    (g := action)
    (f := fun a : Fin K => realMeanGap mean a)).symm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_const]
  have hcount :=
    pullCount_eq_finset_filter_card (action := action) (a := a) (t := n)
  rw [hcount.symm]
  exact nsmul_eq_mul' (realMeanGap mean a) (pullCount action a n)

/-- Pull-count integrability implies integrability of Real mean regret. -/
theorem integrable_realMeanRegret_of_integrable_pullCount
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (mean : Fin K -> Real)
    (action : Omega -> ActionTrace (Fin K))
    (n : Nat)
    (hcount : forall a : Fin K,
      Integrable (fun omega => (pullCount (action omega) a n : Real)) mu) :
    Integrable (fun omega => realMeanRegret mean (action omega) n) mu := by
  let term : Fin K -> Omega -> Real :=
    fun a omega => realMeanGap mean a * (pullCount (action omega) a n : Real)
  have hterm : forall a : Fin K, Integrable (term a) mu := by
    intro a
    exact (hcount a).const_mul (realMeanGap mean a)
  have hsum :
      Integrable
        (fun omega =>
          (Finset.univ : Finset (Fin K)).sum (fun a => term a omega)) mu :=
    IntegrabilitySums.integrable_univ_sum mu term hterm
  have hfun :
      (fun omega => realMeanRegret mean (action omega) n) =
        (fun omega =>
          (Finset.univ : Finset (Fin K)).sum (fun a => term a omega)) := by
    funext omega
    exact realMeanRegret_eq_sum_gap_mul_pullCount mean (action omega) n
  rwa [hfun]

/--
The Bochner expectation of Real mean regret is the gap-weighted sum of expected
pull counts.

This is the expectation half of `REAL-MEAN-REGRET-PULLCOUNT`.  Callers supply
only pull-count integrability; probability-space, policy, reward-law, and
sub-Gaussian contracts remain outside this bookkeeping leaf.
-/
theorem integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (mean : Fin K -> Real)
    (action : Omega -> ActionTrace (Fin K))
    (n : Nat)
    (hcount : forall a : Fin K,
      Integrable (fun omega => (pullCount (action omega) a n : Real)) mu) :
    integral mu (fun omega => realMeanRegret mean (action omega) n) =
      (Finset.univ : Finset (Fin K)).sum
        (fun a =>
          realMeanGap mean a *
            integral mu (fun omega => (pullCount (action omega) a n : Real))) := by
  let term : Fin K -> Omega -> Real :=
    fun a omega => realMeanGap mean a * (pullCount (action omega) a n : Real)
  have hterm : forall a : Fin K, Integrable (term a) mu := by
    intro a
    exact (hcount a).const_mul (realMeanGap mean a)
  have hfun :
      (fun omega => realMeanRegret mean (action omega) n) =
        (fun omega =>
          (Finset.univ : Finset (Fin K)).sum (fun a => term a omega)) := by
    funext omega
    exact realMeanRegret_eq_sum_gap_mul_pullCount mean (action omega) n
  calc
    integral mu (fun omega => realMeanRegret mean (action omega) n) =
        integral mu
          (fun omega =>
            (Finset.univ : Finset (Fin K)).sum (fun a => term a omega)) := by
      rw [hfun]
    _ = (Finset.univ : Finset (Fin K)).sum
          (fun a => integral mu (term a)) :=
      ExpectationBochnerSums.integral_univ_sum mu term hterm
    _ = (Finset.univ : Finset (Fin K)).sum
          (fun a =>
            realMeanGap mean a *
              integral mu (fun omega => (pullCount (action omega) a n : Real))) := by
      apply Finset.sum_congr rfl
      intro a _ha
      simp [term, MeasureTheory.integral_const_mul]

end BanditRLProof
