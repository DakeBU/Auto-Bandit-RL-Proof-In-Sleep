import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

namespace BanditRLProof

namespace DelayedFeedback

/-- Source rounds whose delayed feedback is available before the action at
round `t`.  The strict inequality matches the NeurIPS 2025 delayed-SAPO source:
feedback generated at `s` arrives at the end of `s + delay s`, hence it can be
used for the next action only when `s + delay s < t`. -/
def observedBefore (delay : Nat → Nat) (t : Nat) : Finset Nat :=
  (Finset.range t).filter (fun s => s + delay s < t)

/-- Source rounds before `t` whose feedback is not yet available when the
action at `t` is chosen.  Future source rounds are excluded by `Finset.range
t`. -/
def outstandingAt (delay : Nat → Nat) (t : Nat) : Finset Nat :=
  (Finset.range t).filter (fun s => ¬ s + delay s < t)

/-- Available and outstanding feedback form disjoint parts of the past. -/
theorem observedBefore_disjoint_outstandingAt (delay : Nat → Nat) (t : Nat) :
    Disjoint (observedBefore delay t) (outstandingAt delay t) := by
  rw [Finset.disjoint_left]
  intro s hsObserved hsOutstanding
  exact (Finset.mem_filter.mp hsOutstanding).2
    (Finset.mem_filter.mp hsObserved).2

/-- Every source round before `t` is either available or outstanding. -/
theorem observedBefore_union_outstandingAt (delay : Nat → Nat) (t : Nat) :
    observedBefore delay t ∪ outstandingAt delay t = Finset.range t := by
  ext s
  simp only [Finset.mem_union, observedBefore, outstandingAt,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (hs | hs)
    · exact hs.1
    · exact hs.1
  · intro hs
    by_cases havailable : s + delay s < t
    · exact Or.inl ⟨hs, havailable⟩
    · exact Or.inr ⟨hs, havailable⟩

/-- The available and outstanding counts add up to the number of past source
rounds. -/
theorem card_observedBefore_add_card_outstandingAt
    (delay : Nat → Nat) (t : Nat) :
    (observedBefore delay t).card + (outstandingAt delay t).card = t := by
  rw [← Finset.card_union_of_disjoint
    (observedBefore_disjoint_outstandingAt delay t)]
  rw [observedBefore_union_outstandingAt]
  exact Finset.card_range t

/-- Number of source rounds before `t` whose feedback cannot yet be used by
the action at `t`.  This action-time surface is kept separate from the paper's
end-of-round `sigma(t)` until their one-based/zero-based index bridge is
proved. -/
def outstandingCount (delay : Nat → Nat) (t : Nat) : Nat :=
  (outstandingAt delay t).card

/-- Largest action-time outstanding count through the inclusive horizon. -/
def maxOutstandingBeforeThrough (delay : Nat → Nat) (horizon : Nat) : Nat :=
  (Finset.range (horizon + 1)).sup (outstandingCount delay)

/-- An action-time outstanding count never exceeds the number of past source
rounds. -/
theorem outstandingCount_le_round (delay : Nat → Nat) (t : Nat) :
    outstandingCount delay t ≤ t := by
  rw [outstandingCount]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (Finset.card_range t)

/-- Every action-time outstanding count inside the horizon is bounded by the
finite maximum surface. -/
theorem outstandingCount_le_maxOutstandingBeforeThrough
    (delay : Nat → Nat) {t horizon : Nat} (ht : t ≤ horizon) :
    outstandingCount delay t ≤ maxOutstandingBeforeThrough delay horizon := by
  exact Finset.le_sup
    (s := Finset.range (horizon + 1))
    (f := outstandingCount delay)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))

/-- Convert a one-based paper delay sequence into the zero-based source
carrier used by `outstandingAt`: zero-based source `s` represents paper source
round `s + 1`. -/
def oneBasedDelayShift (delay : Nat → Nat) (s : Nat) : Nat :=
  delay (s + 1)

/-- The paper's end-of-round missing-feedback set, represented on a zero-based
finite carrier.  An element `s` denotes paper round `s + 1`, and the predicate
is exactly `(s + 1) + d_(s+1) > t` for source rounds at most `t`. -/
def paperMissingAtEnd (delay : Nat → Nat) (t : Nat) : Finset Nat :=
  (Finset.range t).filter (fun s => t < (s + 1) + delay (s + 1))

/-- The source paper's one-based end-of-round missing set is exactly the
action-time outstanding set after reindexing source rounds and delays.  This
lemma is the explicit off-by-one bridge; the two surfaces are not identified
by notation alone. -/
theorem paperMissingAtEnd_eq_outstandingAt_oneBasedDelayShift
    (delay : Nat → Nat) (t : Nat) :
    paperMissingAtEnd delay t = outstandingAt (oneBasedDelayShift delay) t := by
  ext s
  simp only [paperMissingAtEnd, outstandingAt, oneBasedDelayShift,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hs, hmissing⟩
    exact ⟨hs, by omega⟩
  · rintro ⟨hs, houtstanding⟩
    exact ⟨hs, by omega⟩

/-- Paper-facing count corresponding to `sigma(t)`, with paper rounds
`1, ..., t` represented by zero-based source indices. -/
def paperMissingCount (delay : Nat → Nat) (t : Nat) : Nat :=
  (paperMissingAtEnd delay t).card

/-- Cardinal form of the one-based/end-of-round indexing bridge. -/
theorem paperMissingCount_eq_outstandingCount_oneBasedDelayShift
    (delay : Nat → Nat) (t : Nat) :
    paperMissingCount delay t = outstandingCount (oneBasedDelayShift delay) t := by
  rw [paperMissingCount, outstandingCount,
    paperMissingAtEnd_eq_outstandingAt_oneBasedDelayShift]

/-- The paper-facing missing count at round `t` is at most `t`. -/
theorem paperMissingCount_le_round (delay : Nat → Nat) (t : Nat) :
    paperMissingCount delay t ≤ t := by
  rw [paperMissingCount_eq_outstandingCount_oneBasedDelayShift]
  exact outstandingCount_le_round (oneBasedDelayShift delay) t

/-- Finite maximum of the paper-facing missing-count surface through an
inclusive horizon. -/
def paperSigmaMaxThrough (delay : Nat → Nat) (horizon : Nat) : Nat :=
  (Finset.range (horizon + 1)).sup (paperMissingCount delay)

/-- Each paper-facing missing count is bounded by its finite maximum through
the declared horizon. -/
theorem paperMissingCount_le_paperSigmaMaxThrough
    (delay : Nat → Nat) {t horizon : Nat} (ht : t ≤ horizon) :
    paperMissingCount delay t ≤ paperSigmaMaxThrough delay horizon := by
  exact Finset.le_sup
    (s := Finset.range (horizon + 1))
    (f := paperMissingCount delay)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))

end DelayedFeedback

end BanditRLProof
