import Mathlib.Probability.Martingale.Basic

/-!
# Martingale-difference witness surface

This module exposes a small finite-prefix contract for martingale-difference
increments.  It deliberately stays below optional stopping or final regret
theorems: the witness records integrability, adaptedness, and succ-indexed
conditional mean-zero facts in the shape used by the local bandit
filtration/concentration route.
-/

namespace BanditRLProof
namespace MartingaleDiff

open MeasureTheory

/--
Global succ-indexed martingale-difference witness.

This is the all-time version of `SuccMartingaleDifferencePrefix`.  It records
the local hypotheses needed to build the Mathlib martingale of partial sums.
-/
structure SuccMartingaleDifference
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega)
    (F : Filtration Nat mOmega)
    (Y : Nat -> Omega -> Real) : Prop where
  stronglyAdapted : StronglyAdapted F Y
  integrable : forall t, Integrable (Y t) mu
  condExp_succ_eq_zero :
    forall i,
      Filter.EventuallyEq (ae mu)
        (condExp (F i) mu (Y (i + 1)))
        (fun _omega => (0 : Real))

/--
Finite-prefix succ-indexed martingale-difference witness.

For a process `Y`, this records that the prefix up to `n` is integrable and
adapted, and that each later increment `Y (i + 1)` has zero conditional
expectation against filtration level `i`.  This is the local bridge between the
compiled conditional-mean-zero leaves and later martingale or concentration
consumers.
-/
structure SuccMartingaleDifferencePrefix
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega)
    (F : Filtration Nat mOmega)
    (Y : Nat -> Omega -> Real)
    (n : Nat) : Prop where
  stronglyAdapted : StronglyAdapted F Y
  integrable : forall t, t < n -> Integrable (Y t) mu
  condExp_succ_eq_zero :
    forall i, i + 1 < n ->
      Filter.EventuallyEq (ae mu)
        (condExp (F i) mu (Y (i + 1)))
        (fun _omega => (0 : Real))

namespace SuccMartingaleDifference

theorem toPrefix
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega}
    {F : Filtration Nat mOmega}
    {Y : Nat -> Omega -> Real}
    (h : SuccMartingaleDifference mu F Y)
    (n : Nat) :
    SuccMartingaleDifferencePrefix mu F Y n where
  stronglyAdapted := h.stronglyAdapted
  integrable := fun t _ht => h.integrable t
  condExp_succ_eq_zero := fun i _hi => h.condExp_succ_eq_zero i

theorem stronglyAdapted'
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega}
    {F : Filtration Nat mOmega}
    {Y : Nat -> Omega -> Real}
    (h : SuccMartingaleDifference mu F Y) :
    StronglyAdapted F Y :=
  h.stronglyAdapted

theorem integrable'
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega}
    {F : Filtration Nat mOmega}
    {Y : Nat -> Omega -> Real}
    (h : SuccMartingaleDifference mu F Y)
    (t : Nat) :
    Integrable (Y t) mu :=
  h.integrable t

theorem condExp_succ_ae_eq_zero
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega}
    {F : Filtration Nat mOmega}
    {Y : Nat -> Omega -> Real}
    (h : SuccMartingaleDifference mu F Y)
    (i : Nat) :
    Filter.EventuallyEq (ae mu)
      (condExp (F i) mu (Y (i + 1)))
      (fun _omega => (0 : Real)) :=
  h.condExp_succ_eq_zero i

end SuccMartingaleDifference

namespace SuccMartingaleDifferencePrefix

theorem stronglyAdapted'
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega}
    {F : Filtration Nat mOmega}
    {Y : Nat -> Omega -> Real}
    {n : Nat}
    (h : SuccMartingaleDifferencePrefix mu F Y n) :
    StronglyAdapted F Y :=
  h.stronglyAdapted

theorem integrable_of_lt
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega}
    {F : Filtration Nat mOmega}
    {Y : Nat -> Omega -> Real}
    {n : Nat}
    (h : SuccMartingaleDifferencePrefix mu F Y n)
    {t : Nat} (ht : t < n) :
    Integrable (Y t) mu :=
  h.integrable t ht

theorem condExp_succ_ae_eq_zero
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega}
    {F : Filtration Nat mOmega}
    {Y : Nat -> Omega -> Real}
    {n : Nat}
    (h : SuccMartingaleDifferencePrefix mu F Y n)
    {i : Nat} (hi : i + 1 < n) :
    Filter.EventuallyEq (ae mu)
      (condExp (F i) mu (Y (i + 1)))
      (fun _omega => (0 : Real)) :=
  h.condExp_succ_eq_zero i hi

end SuccMartingaleDifferencePrefix

/--
Centered reward process obtained by subtracting a predictable or otherwise
chosen baseline from a raw reward process.

The baseline is allowed to be random; the martingale-difference builder below
therefore asks directly for adaptedness, integrability, and conditional
mean-zero of this centered process.
-/
def centeredRewardProcess
    {Omega : Type u}
    (reward baseline : Nat -> Omega -> Real) :
    Nat -> Omega -> Real :=
  fun t omega => reward t omega - baseline t omega

/--
Build the global succ-indexed martingale-difference witness for a centered
reward process from the exact three local contracts used by Mathlib:
adaptedness, integrability, and succ-indexed conditional mean zero.
-/
theorem succMartingaleDifference_centeredRewardProcess_of_condExp
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega)
    {F : Filtration Nat mOmega}
    (reward baseline : Nat -> Omega -> Real)
    (hadapted :
      StronglyAdapted F (centeredRewardProcess reward baseline))
    (hintegrable :
      forall t, Integrable (centeredRewardProcess reward baseline t) mu)
    (hcond :
      forall i,
        Filter.EventuallyEq (ae mu)
          (condExp (F i) mu
            (centeredRewardProcess reward baseline (i + 1)))
          (fun _omega => (0 : Real))) :
    SuccMartingaleDifference mu F
      (centeredRewardProcess reward baseline) where
  stronglyAdapted := hadapted
  integrable := hintegrable
  condExp_succ_eq_zero := hcond

/--
Finite-prefix version of
`succMartingaleDifference_centeredRewardProcess_of_condExp`.
-/
theorem succMartingaleDifferencePrefix_centeredRewardProcess_of_condExp
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega)
    {F : Filtration Nat mOmega}
    (reward baseline : Nat -> Omega -> Real)
    (n : Nat)
    (hadapted :
      StronglyAdapted F (centeredRewardProcess reward baseline))
    (hintegrable :
      forall t, t < n ->
        Integrable (centeredRewardProcess reward baseline t) mu)
    (hcond :
      forall i, i + 1 < n ->
        Filter.EventuallyEq (ae mu)
          (condExp (F i) mu
            (centeredRewardProcess reward baseline (i + 1)))
          (fun _omega => (0 : Real))) :
    SuccMartingaleDifferencePrefix mu F
      (centeredRewardProcess reward baseline) n where
  stronglyAdapted := hadapted
  integrable := hintegrable
  condExp_succ_eq_zero := hcond

/--
Partial sums of a succ-indexed martingale-difference process.

The sum starts at `Y 1`, so the increment from time `i` to `i + 1` is
definitionally `Y (i + 1)`, matching Mathlib's martingale theorem
`martingale_of_condExp_sub_eq_zero_nat`.
-/
noncomputable def partialSumsSucc
    {Omega : Type u}
    (Y : Nat -> Omega -> Real) :
    Nat -> Omega -> Real :=
  fun n => (Finset.range n).sum (fun i => Y (i + 1))

/--
The partial sums of a global succ-indexed martingale-difference process form a
Mathlib martingale.

This is a thin wrapper around
`MeasureTheory.martingale_of_condExp_sub_eq_zero_nat`.  It does not assert
optional stopping, concentration, or final regret; it only upgrades the local
conditional-mean-zero increment contract to Mathlib's martingale API.
-/
theorem martingale_partialSumsSucc_of_succMartingaleDifference
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {F : Filtration Nat mOmega}
    {Y : Nat -> Omega -> Real}
    (h : SuccMartingaleDifference mu F Y) :
    Martingale (partialSumsSucc Y) F mu := by
  have h_adapted : StronglyAdapted F (partialSumsSucc Y) := by
    intro n
    change StronglyMeasurable[F n]
      ((Finset.range n).sum (fun i => Y (i + 1)))
    refine (Finset.range n).stronglyMeasurable_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact h.stronglyAdapted.stronglyMeasurable_le (Nat.succ_le_of_lt hi)
  have h_integrable : forall n, Integrable (partialSumsSucc Y n) mu := by
    intro n
    change Integrable
      ((Finset.range n).sum (fun i => Y (i + 1))) mu
    exact
      MeasureTheory.integrable_finset_sum' (Finset.range n) fun i _hi =>
        h.integrable (i + 1)
  refine
    MeasureTheory.martingale_of_condExp_sub_eq_zero_nat
      h_adapted h_integrable ?_
  intro i
  have hdiff :
      (partialSumsSucc Y (i + 1) - partialSumsSucc Y i) =
        Y (i + 1) := by
    funext omega
    simp [partialSumsSucc, Pi.sub_apply, Finset.sum_range_succ]
  simpa [hdiff] using h.condExp_succ_eq_zero i

/--
The partial sums of a global centered reward process form a Mathlib martingale
once the centered process satisfies the martingale-difference contracts.
-/
theorem martingale_partialSumsSucc_centeredRewardProcess_of_condExp
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {F : Filtration Nat mOmega}
    (reward baseline : Nat -> Omega -> Real)
    (hadapted :
      StronglyAdapted F (centeredRewardProcess reward baseline))
    (hintegrable :
      forall t, Integrable (centeredRewardProcess reward baseline t) mu)
    (hcond :
      forall i,
        Filter.EventuallyEq (ae mu)
          (condExp (F i) mu
            (centeredRewardProcess reward baseline (i + 1)))
          (fun _omega => (0 : Real))) :
    Martingale
      (partialSumsSucc (centeredRewardProcess reward baseline)) F mu := by
  exact
    martingale_partialSumsSucc_of_succMartingaleDifference mu
      (succMartingaleDifference_centeredRewardProcess_of_condExp
        mu reward baseline hadapted hintegrable hcond)

end MartingaleDiff
end BanditRLProof
