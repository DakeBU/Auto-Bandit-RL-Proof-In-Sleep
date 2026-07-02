import Mathlib.MeasureTheory.Integral.Bochner.Basic
import BanditRLProof.ExpectationBochnerSums
import BanditRLProof.RegretDecomposition

/-!
# Bochner expected-regret pull-count decomposition

This module lifts the deterministic `REGRET-PULLCOUNT` equality to a
Real-valued Bochner expectation statement.  It stays at the bookkeeping layer:
the only probabilistic regularity assumption is integrability of each finite
horizon pull-count random variable after casting to `Real`.
-/

namespace BanditRLProof

open MeasureTheory

universe u

private theorem real_pseudoRegret_eq_univ_sum_gap_mul_natCast_pullCount
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (n : Nat) :
    ((pseudoRegret model action n : Rat) : Real) =
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K =>
          ((model.gap a : Rat) : Real) *
            ((pullCount action a n : Nat) : Real)) := by
  simp [pseudoRegret_eq_finset_sum_gap_mul_pullCount]

/--
If every finite-horizon pull count is integrable after casting to `Real`, then
the corresponding Real-valued pseudo-regret is integrable.

This is the regularity adapter used by the Bochner expected-regret
decomposition.  It does not prove measurability or integrability from a policy
model; callers provide the pull-count integrability witnesses.
-/
theorem integrable_real_pseudoRegret_of_integrable_pullCount
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (n : Nat)
    (hcount : forall a : Fin K,
      Integrable
        (fun omega : Omega =>
          ((pullCount (action omega) a n : Nat) : Real)) mu) :
    Integrable
      (fun omega : Omega =>
        ((pseudoRegret model (action omega) n : Rat) : Real)) mu := by
  let term : Fin K -> Omega -> Real :=
    fun a omega =>
      ((model.gap a : Rat) : Real) *
        ((pullCount (action omega) a n : Nat) : Real)
  have hterm : forall a : Fin K, Integrable (term a) mu := by
    intro a
    exact (hcount a).const_mul ((model.gap a : Rat) : Real)
  have hsum :
      Integrable
        (fun omega : Omega =>
          (Finset.univ : Finset (Fin K)).sum
            (fun a : Fin K => term a omega)) mu := by
    exact
      IntegrabilitySums.integrable_univ_sum
        (mu := mu)
        (f := term)
        (hf := hterm)
  have hfun :
      (fun omega : Omega =>
          ((pseudoRegret model (action omega) n : Rat) : Real))
        =
      (fun omega : Omega =>
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => term a omega)) := by
    funext omega
    exact
      real_pseudoRegret_eq_univ_sum_gap_mul_natCast_pullCount
        (model := model)
        (action := action omega)
        (n := n)
  rwa [hfun]

/--
The Real-valued Bochner expectation of pseudo-regret is the finite sum of each
arm gap multiplied by the Bochner expectation of that arm's pull count.

This is the local `EXP-REGRET-PULLCOUNT` leaf.  It consumes the deterministic
`REGRET-PULLCOUNT` bridge and the Mathlib-backed `EXP-FINITE-SUM` wrapper.
-/
theorem integral_real_pseudoRegret_eq_sum_gap_mul_integral_pullCount
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (n : Nat)
    (hcount : forall a : Fin K,
      Integrable
        (fun omega : Omega =>
          ((pullCount (action omega) a n : Nat) : Real)) mu) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        ((pseudoRegret model (action omega) n : Rat) : Real))
      =
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ((model.gap a : Rat) : Real) *
          MeasureTheory.integral mu
            (fun omega : Omega =>
              ((pullCount (action omega) a n : Nat) : Real))) := by
  let term : Fin K -> Omega -> Real :=
    fun a omega =>
      ((model.gap a : Rat) : Real) *
        ((pullCount (action omega) a n : Nat) : Real)
  have hterm : forall a : Fin K, Integrable (term a) mu := by
    intro a
    exact (hcount a).const_mul ((model.gap a : Rat) : Real)
  have hfun :
      (fun omega : Omega =>
          ((pseudoRegret model (action omega) n : Rat) : Real))
        =
      (fun omega : Omega =>
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => term a omega)) := by
    funext omega
    exact
      real_pseudoRegret_eq_univ_sum_gap_mul_natCast_pullCount
        (model := model)
        (action := action omega)
        (n := n)
  calc
    MeasureTheory.integral mu
      (fun omega : Omega =>
        ((pseudoRegret model (action omega) n : Rat) : Real))
        =
      MeasureTheory.integral mu
        (fun omega : Omega =>
          (Finset.univ : Finset (Fin K)).sum
            (fun a : Fin K => term a omega)) := by
          rw [hfun]
    _ =
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K =>
          MeasureTheory.integral mu (term a)) := by
          exact
            ExpectationBochnerSums.integral_univ_sum
              (mu := mu)
              (f := term)
              (hf := hterm)
    _ =
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K =>
          ((model.gap a : Rat) : Real) *
            MeasureTheory.integral mu
              (fun omega : Omega =>
                ((pullCount (action omega) a n : Nat) : Real))) := by
          apply Finset.sum_congr rfl
          intro a _ha
          simp [term, MeasureTheory.integral_const_mul]

end BanditRLProof
