import Mathlib

/-!
# A source-faithful deterministic core of Delayed SAPO Lemma D.11

The frozen Delayed SAPO source uses a Markov-style count for stochastic loss
gaps: at most half of the gaps are greater than `2 * mu`.  This formalization
promotes exactly the nonnegative domain used by that application and handles
the zero-average case separately.

This file records the deterministic statement used by the bandit
application.  It treats the empty family and zero average explicitly, and
then specializes the result to stochastic loss gaps
`mean i - mean optimal`.  It does not construct an Algorithm-5 trajectory,
the BSC/EAP branches, a stochastic good event, or the later D.12/regret
endpoints.
-/

namespace BanditRLProof

namespace DelayedFeedback

/-- Arithmetic mean of a finite family of real gaps.  Lean's total division
makes this definition equal to zero when `K = 0`; the counting theorem below
handles that empty case before using the denominator. -/
noncomputable def finiteAverageGap {K : Nat} (gap : Fin K -> Real) : Real :=
  (∑ i : Fin K, gap i) / (K : Real)

/-- Indices whose gaps are strictly greater than twice the finite average,
matching the strict word "greater" in the source statement of Lemma D.11. -/
noncomputable def aboveTwiceAverageGap {K : Nat}
    (gap : Fin K -> Real) : Finset (Fin K) :=
  Finset.univ.filter fun i => 2 * finiteAverageGap gap < gap i

/-- Nonnegative-domain deterministic content used by the source's Lemma D.11.

Nonnegativity is explicit rather than extending the promoted contract to an
arbitrary signed family.  The theorem includes `K = 0`; for positive `K`, its
proof separately closes the zero-average branch before cancelling the
positive average in the usual counting/Markov argument. -/
theorem two_mul_card_aboveTwiceAverageGap_le
    {K : Nat} (gap : Fin K -> Real) (hgap : forall i, 0 <= gap i) :
    2 * (aboveTwiceAverageGap gap).card <= K := by
  classical
  by_cases hK : K = 0
  · subst K
    simp [aboveTwiceAverageGap]
  have hKpos : 0 < K := Nat.pos_of_ne_zero hK
  have hKcastPos : (0 : Real) < K := by exact_mod_cast hKpos
  have hsumNonneg : 0 <= ∑ i : Fin K, gap i := by
    exact Finset.sum_nonneg fun i _ => hgap i
  have haverageNonneg : 0 <= finiteAverageGap gap := by
    exact div_nonneg hsumNonneg hKcastPos.le
  by_cases haverageZero : finiteAverageGap gap = 0
  · have hsumZero : (∑ i : Fin K, gap i) = 0 := by
      rw [finiteAverageGap, div_eq_zero_iff] at haverageZero
      exact haverageZero.resolve_right (by positivity)
    have hgapZero : forall i : Fin K, gap i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_hj : j ∈ (Finset.univ : Finset (Fin K))) => hgap j)).mp
          hsumZero i (Finset.mem_univ i)
    have hlargeEmpty : aboveTwiceAverageGap gap = ∅ := by
      ext i
      simp [aboveTwiceAverageGap, haverageZero, hgapZero i]
    simp [hlargeEmpty]
  have haveragePos : 0 < finiteAverageGap gap :=
    lt_of_le_of_ne haverageNonneg (Ne.symm haverageZero)
  by_cases hlargeNonempty : (aboveTwiceAverageGap gap).Nonempty
  · have hstrictSum :
        (aboveTwiceAverageGap gap).sum
              (fun _ => 2 * finiteAverageGap gap) <
            (aboveTwiceAverageGap gap).sum gap := by
      apply Finset.sum_lt_sum_of_nonempty hlargeNonempty
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hsubsetSum :
        (aboveTwiceAverageGap gap).sum gap <=
            (Finset.univ : Finset (Fin K)).sum gap := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro i _hi _hnot
      exact hgap i
    have hsumIdentity :
        (Finset.univ : Finset (Fin K)).sum gap =
            finiteAverageGap gap * (K : Real) := by
      rw [finiteAverageGap]
      field_simp
    have hcardReal :
        (2 : Real) * ((aboveTwiceAverageGap gap).card : Real) < (K : Real) := by
      have hconstantSum :
          (aboveTwiceAverageGap gap).sum
                (fun _ => 2 * finiteAverageGap gap) =
              ((aboveTwiceAverageGap gap).card : Real) *
                (2 * finiteAverageGap gap) := by
        simp
      rw [hconstantSum] at hstrictSum
      rw [hsumIdentity] at hsubsetSum
      nlinarith
    have hcardNat : 2 * (aboveTwiceAverageGap gap).card < K := by
      exact_mod_cast hcardReal
    exact Nat.le_of_lt hcardNat
  · have hlargeEmpty : aboveTwiceAverageGap gap = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hlargeNonempty
    simp [hlargeEmpty]

/-- The stochastic loss gap convention used by the delayed-SAPO source:
smaller mean loss is better, so the gap of arm `i` is
`mean i - mean optimal`. -/
def sourceStochasticLossGap {K : Nat}
    (mean : Fin K -> Real) (optimal i : Fin K) : Real :=
  mean i - mean optimal

/-- An optimal arm makes every source stochastic loss gap nonnegative. -/
theorem sourceStochasticLossGap_nonneg
    {K : Nat} (mean : Fin K -> Real) (optimal : Fin K)
    (hoptimal : forall i, mean optimal <= mean i) (i : Fin K) :
    0 <= sourceStochasticLossGap mean optimal i := by
  unfold sourceStochasticLossGap
  linarith [hoptimal i]

/-- Bandit specialization of the nonnegative-domain D.11 counting statement.

Among the `K` stochastic loss gaps from an optimal arm, strictly fewer than
half can exceed twice their average (and hence their cardinality is at most
half).  This is a deterministic producer; it does not assume or claim any
generated delayed-feedback probability law. -/
theorem two_mul_card_sourceStochasticLossGap_aboveTwiceAverage_le
    {K : Nat} (mean : Fin K -> Real) (optimal : Fin K)
    (hoptimal : forall i, mean optimal <= mean i) :
    2 * (aboveTwiceAverageGap
      (sourceStochasticLossGap mean optimal)).card <= K := by
  apply two_mul_card_aboveTwiceAverageGap_le
  intro i
  exact sourceStochasticLossGap_nonneg mean optimal hoptimal i

end DelayedFeedback

end BanditRLProof
