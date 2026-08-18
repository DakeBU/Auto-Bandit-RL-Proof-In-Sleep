import BanditRLProof.DelayedFeedback.ActiveAllocation

namespace BanditRLProof

namespace DelayedFeedback

open scoped BigOperators

/-- Inputs read by Algorithm 5 line 7 when it processes one newly available
feedback item.  This is deliberately an elimination snapshot rather than a
claim that the full Delayed SAPO state machine has already been implemented. -/
structure DelayedSAPOEliminationSnapshot (K : Nat) where
  active : Finset (Fin K)
  empiricalMean : Fin K → ℝ
  empiricalWidth : Fin K → ℝ
  ucbStar : ℝ

namespace DelayedSAPOEliminationSnapshot

/-- Arms selected by the strict elimination test in Algorithm 5 line 7. -/
noncomputable def eliminated {K : Nat}
    (snapshot : DelayedSAPOEliminationSnapshot K) :
    Finset (Fin K) :=
  snapshot.active.filter (fun i =>
    snapshot.ucbStar <
      snapshot.empiricalMean i - (9 : ℝ) * snapshot.empiricalWidth i)

/-- Active set after Algorithm 5 line 8 removes every arm selected by line 7. -/
noncomputable def remainingActive {K : Nat}
    (snapshot : DelayedSAPOEliminationSnapshot K) :
    Finset (Fin K) :=
  snapshot.active \ snapshot.eliminated

@[simp]
theorem mem_eliminated_iff {K : Nat}
    (snapshot : DelayedSAPOEliminationSnapshot K) (i : Fin K) :
    i ∈ snapshot.eliminated ↔
      i ∈ snapshot.active ∧
        snapshot.ucbStar <
          snapshot.empiricalMean i -
            (9 : ℝ) * snapshot.empiricalWidth i := by
  simp [eliminated]

@[simp]
theorem mem_remainingActive_iff {K : Nat}
    (snapshot : DelayedSAPOEliminationSnapshot K) (i : Fin K) :
    i ∈ snapshot.remainingActive ↔
      i ∈ snapshot.active ∧
        snapshot.empiricalMean i -
            (9 : ℝ) * snapshot.empiricalWidth i ≤ snapshot.ucbStar := by
  simp only [remainingActive, Finset.mem_sdiff, mem_eliminated_iff, not_and_or]
  by_cases hactive : i ∈ snapshot.active
  · simp [hactive, not_lt]
  · simp [hactive]

/-- The two source conditions used in the deterministic core of Lemma D.9:
the empirical mean of the optimal arm lies in its good-event confidence
interval, and the source's `ucbStar` remains an upper certificate for the
optimal mean.  The event probability establishing these fields is a separate
concentration obligation. -/
structure OptimalArmSurvivalCertificate {K : Nat}
    (snapshot : DelayedSAPOEliminationSnapshot K)
    (mean : Fin K → ℝ) (optimal : Fin K) : Prop where
  optimal_active : optimal ∈ snapshot.active
  width_nonnegative : 0 ≤ snapshot.empiricalWidth optimal
  empirical_confidence :
    |snapshot.empiricalMean optimal - mean optimal| ≤
      snapshot.empiricalWidth optimal
  optimalMean_le_ucbStar : mean optimal ≤ snapshot.ucbStar

/-- Deterministic core of source Lemma D.9: on the relevant stochastic
good-event projections, Algorithm 5's strict line-7 test cannot eliminate the
certified optimal arm. -/
theorem optimal_mem_remainingActive_of_certificate {K : Nat}
    (snapshot : DelayedSAPOEliminationSnapshot K)
    (mean : Fin K → ℝ) (optimal : Fin K)
    (certificate : OptimalArmSurvivalCertificate snapshot mean optimal) :
    optimal ∈ snapshot.remainingActive := by
  rw [mem_remainingActive_iff]
  refine ⟨certificate.optimal_active, ?_⟩
  have hempiricalUpper :
      snapshot.empiricalMean optimal ≤
        mean optimal + snapshot.empiricalWidth optimal := by
    have hupper := (abs_le.mp certificate.empirical_confidence).2
    linarith
  linarith [certificate.width_nonnegative,
    certificate.optimalMean_le_ucbStar]

/-- Consequently the post-elimination active set is nonempty.  This closes
the exact nonemptiness premise required by Algorithm 5 line 15's residual
allocation. -/
theorem remainingActive_nonempty_of_certificate {K : Nat}
    (snapshot : DelayedSAPOEliminationSnapshot K)
    (mean : Fin K → ℝ) (optimal : Fin K)
    (certificate : OptimalArmSurvivalCertificate snapshot mean optimal) :
    snapshot.remainingActive.Nonempty :=
  ⟨optimal, optimal_mem_remainingActive_of_certificate
    snapshot mean optimal certificate⟩

/-- Under the same optimal-arm survival certificate, the probability vector
computed after line 8 and line 15 has total mass exactly one.  EAP still has
to establish coordinate nonnegativity and the inactive-mass upper bound. -/
theorem sum_delayedSAPOProbability_after_elimination_eq_one {K : Nat}
    (snapshot : DelayedSAPOEliminationSnapshot K)
    (mean : Fin K → ℝ) (optimal : Fin K)
    (certificate : OptimalArmSurvivalCertificate snapshot mean optimal)
    (inactiveProbability : Fin K → ℝ) :
    ∑ i, delayedSAPOProbability snapshot.remainingActive
      inactiveProbability i = 1 := by
  exact sum_delayedSAPOProbability_eq_one
    snapshot.remainingActive inactiveProbability
    (remainingActive_nonempty_of_certificate
      snapshot mean optimal certificate)

end DelayedSAPOEliminationSnapshot

end DelayedFeedback

end BanditRLProof
