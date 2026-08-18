import BanditRLProof.DelayedFeedback.Accounting

namespace BanditRLProof

namespace DelayedFeedback

/-- Feedback source rounds that are available before action `t` but have not
yet been processed.  This is the set-level content of Algorithm 5's
`B(t) \ S`; the source sequence order remains a later algorithm-state choice. -/
def newlyObservedBefore
    (delay : Nat → Nat) (processed : Finset Nat) (t : Nat) : Finset Nat :=
  observedBefore delay t \ processed

/-- Strictly available feedback remains available at every later action
round. -/
theorem observedBefore_mono
    (delay : Nat → Nat) {t u : Nat} (htu : t ≤ u) :
    observedBefore delay t ⊆ observedBefore delay u := by
  intro s hs
  rw [observedBefore, Finset.mem_filter] at hs ⊢
  exact ⟨Finset.mem_range.mpr (lt_of_lt_of_le
    (Finset.mem_range.mp hs.1) htu), lt_of_lt_of_le hs.2 htu⟩

/-- A source round is never both already processed and newly observed. -/
theorem processed_disjoint_newlyObservedBefore
    (delay : Nat → Nat) (processed : Finset Nat) (t : Nat) :
    Disjoint processed (newlyObservedBefore delay processed t) := by
  rw [Finset.disjoint_left]
  intro s hprocessed hnew
  exact (Finset.mem_sdiff.mp hnew).2 hprocessed

/-- If all processed rounds were legitimately available, adjoining every new
arrival yields exactly the current available set. -/
theorem processed_union_newlyObservedBefore
    (delay : Nat → Nat) (processed : Finset Nat) (t : Nat)
    (hprocessed : processed ⊆ observedBefore delay t) :
    processed ∪ newlyObservedBefore delay processed t =
      observedBefore delay t := by
  ext s
  simp only [Finset.mem_union, newlyObservedBefore, Finset.mem_sdiff]
  constructor
  · rintro (hs | hs)
    · exact hprocessed hs
    · exact hs.1
  · intro havailable
    by_cases hs : s ∈ processed
    · exact Or.inl hs
    · exact Or.inr ⟨havailable, hs⟩

/-- The update obtained by processing every currently new arrival is the
current available set. -/
def processAllNew
    (delay : Nat → Nat) (processed : Finset Nat) (t : Nat) : Finset Nat :=
  processed ∪ newlyObservedBefore delay processed t

theorem processAllNew_eq_observedBefore
    (delay : Nat → Nat) (processed : Finset Nat) (t : Nat)
    (hprocessed : processed ⊆ observedBefore delay t) :
    processAllNew delay processed t = observedBefore delay t := by
  exact processed_union_newlyObservedBefore delay processed t hprocessed

/-- A completed earlier available set is a valid processed prefix later. -/
theorem previousObservedBefore_subset_current
    (delay : Nat → Nat) {t u : Nat} (htu : t ≤ u) :
    observedBefore delay t ⊆ observedBefore delay u :=
  observedBefore_mono delay htu

/-- Starting from the fully processed set at an earlier round and processing
all arrivals through a later round yields exactly the later available set. -/
theorem processAllNew_from_previous_eq_current
    (delay : Nat → Nat) {t u : Nat} (htu : t ≤ u) :
    processAllNew delay (observedBefore delay t) u =
      observedBefore delay u := by
  exact processAllNew_eq_observedBefore delay (observedBefore delay t) u
    (observedBefore_mono delay htu)

/-- Outstanding feedback cannot appear in the newly observed batch at the
same action time. -/
theorem outstandingAt_disjoint_newlyObservedBefore
    (delay : Nat → Nat) (processed : Finset Nat) (t : Nat) :
    Disjoint (outstandingAt delay t)
      (newlyObservedBefore delay processed t) := by
  rw [Finset.disjoint_left]
  intro s houtstanding hnew
  exact (Finset.mem_filter.mp houtstanding).2
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hnew).1).2

end DelayedFeedback

end BanditRLProof
