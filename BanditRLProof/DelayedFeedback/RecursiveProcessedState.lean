import BanditRLProof.DelayedFeedback.ProcessedPrefixCounts

/-!
# Processed trace-summary adapter for Delayed SAPO

This module makes one deterministic interface preceding the probabilistic count
clause in source Definition D.1 / Lemma D.4 explicit.  A processed trace summary
stores the source round of every processed item and reads the allocation that
was present at that source round.  It never reconstructs a source-time
probability from the later processing-time state.  Source indices are unique
and carry the strict availability witness `s + d_s < t` used by Algorithm 5.

The summary is not constructed from the recursive Algorithm-5 transition
system.  Establishing such a generated-trajectory-to-summary producer remains
open, so this module must not be reported as a full state-to-ledger projection.

The only stochastic input is `D4CountClause`, which records the two displayed
count inequalities.  Their probability on a generated Delayed-SAPO trajectory
is deliberately not proved here.  In particular, this module does not claim
source Lemmas D.4, D.10, D.12, main-text Lemma 4.2, or either regret endpoint.
-/

namespace BanditRLProof

namespace DelayedFeedback

/-- Source-shaped deterministic summary of a Delayed-SAPO processed trace.

`sourceIndex` is an ordered processing ledger, not a chronological source-round
prefix: feedback from a later source round may be processed before feedback
from an earlier source round.  Its entries are distinct and satisfy the exact
strict availability test at `currentActionRound`.  `activeAtSourceRound`
records the line-15 sampling set at past source rounds and is antitone because
Algorithm 5 only removes arms.  The possibly intra-round `currentActive` set is
stored separately.  Its containment in every ledger source set is an explicit
trace-summary invariant that a future Algorithm-5 producer must prove.  The
current empirical surfaces are likewise separate from the source-time
allocations used by the ledger.

This record is an interface summary, not a proof that Algorithm 5 generates
the supplied fields. -/
structure DelayedSAPOProcessedTraceSummary (K : Nat) where
  length : Nat
  sourceIndex : Fin length -> Nat
  sourceIndex_injective : Function.Injective sourceIndex
  currentActionRound : Nat
  delayAt : Nat -> Nat
  source_available : forall q,
    sourceIndex q + delayAt (sourceIndex q) < currentActionRound
  activeAtSourceRound : Nat -> Finset (Fin K)
  sourceActive_antitone : Antitone activeAtSourceRound
  currentActive : Finset (Fin K)
  currentActive_subset_sourceActive : forall q,
    currentActive <= activeAtSourceRound (sourceIndex q)
  chosenArmAt : Nat -> Fin K
  inactiveProbabilityAt : Nat -> Fin K -> Real
  empiricalMean : Fin K -> Real
  importanceUpper : Fin K -> Real
  previousEmpiricalUpper : Fin K -> Real
  ucbStar : Real

namespace DelayedSAPOProcessedTraceSummary

/-- Read every processed entry at its recorded source round. -/
def toProcessedPrefix {K : Nat}
    (state : DelayedSAPOProcessedTraceSummary K) :
    DelayedSAPOProcessedPrefix K where
  length := state.length
  activeAtSource q := state.activeAtSourceRound (state.sourceIndex q)
  inactiveProbabilityAtSource q :=
    state.inactiveProbabilityAt (state.sourceIndex q)
  chosenArmAtSource q := state.chosenArmAt (state.sourceIndex q)
  previousEmpiricalUpper := state.previousEmpiricalUpper

/-- The exact source empirical width at the current processed state. -/
noncomputable def empiricalWidthAt {K : Nat}
    (state : DelayedSAPOProcessedTraceSummary K)
    (horizon : Nat) (i : Fin K) : Real :=
  sourceEmpiricalWidthScale (2 * Real.log (horizon : Real))
    (state.toProcessedPrefix.processedPullCount i : Real)

/-- The recursive empirical UCB printed by the source, evaluated from the
current empirical mean, the current processed count, and the preceding UCB. -/
noncomputable def empiricalUpperAt {K : Nat}
    (state : DelayedSAPOProcessedTraceSummary K)
    (horizon : Nat) (i : Fin K) : Real :=
  min (state.empiricalMean i + state.empiricalWidthAt horizon i)
    (state.previousEmpiricalUpper i)

/-- Confidence snapshot projected from the supplied trace summary.  The width
and recursive empirical UCB are definitions here, rather than certificate
premises. -/
noncomputable def toConfidenceSnapshot {K : Nat}
    (state : DelayedSAPOProcessedTraceSummary K) (horizon : Nat) :
    DelayedSAPOSourceConfidenceSnapshot K where
  active := state.currentActive
  empiricalMean := state.empiricalMean
  empiricalWidth := state.empiricalWidthAt horizon
  ucbStar := state.ucbStar
  empiricalUpper := state.empiricalUpperAt horizon
  importanceUpper := state.importanceUpper

/-- The two armwise count inequalities printed in source Definition D.1 and
used by source Lemma D.4.  This is the stochastic boundary of the present
module: proving that it holds simultaneously with probability at least
`1 - 2 / T` on the generated trajectory remains open. -/
structure D4CountClause {K : Nat}
    (state : DelayedSAPOProcessedTraceSummary K)
    (horizon : Nat) : Prop where
  count_lower : forall i,
    (1 / 2 : Real) * state.toProcessedPrefix.expectedPullMass i -
        3 * Real.log (horizon : Real) <=
      (state.toProcessedPrefix.processedPullCount i : Real)
  count_upper : forall i,
    (state.toProcessedPrefix.processedPullCount i : Real) <=
      2 * state.toProcessedPrefix.expectedPullMass i +
        12 * Real.log (horizon : Real)

/-- Expose the trace-summary invariant that every arm in the intra-round current
set was active at every source round in the processed ledger.  Producing this
invariant from Algorithm 5 is deliberately outside this adapter. -/
theorem currentActive_subset_activeAt_sourceIndex {K : Nat}
    (state : DelayedSAPOProcessedTraceSummary K) (q : Fin state.length) :
    state.currentActive <=
      state.activeAtSourceRound (state.sourceIndex q) := by
  exact state.currentActive_subset_sourceActive q

/-- Deterministic trace-summary adapter for the processed-prefix count
certificate.  Source-time allocation data come from `toProcessedPrefix`,
active persistence is an explicit trace-summary invariant, and the two count
bounds are the explicit D.4 boundary.  No width comparison or gap conclusion
is assumed. -/
theorem toProcessedPrefixCountCertificate
    {K : Nat} [Nonempty (Fin K)]
    (state : DelayedSAPOProcessedTraceSummary K)
    (horizon : Nat) (hD4 : state.D4CountClause horizon) :
    DelayedSAPOProcessedPrefixCountCertificate
      (state.toConfidenceSnapshot horizon)
      state.toProcessedPrefix horizon where
  active_persistence := by
    intro q
    simpa [toConfidenceSnapshot, toProcessedPrefix] using
      state.currentActive_subset_activeAt_sourceIndex q
  count_lower := hD4.count_lower
  count_upper := hD4.count_upper
  empiricalWidth_eq_source := by
    intro i
    rfl
  empiricalUpper_eq_source := by
    intro i
    rfl

/-- Downstream same-snapshot factor-twenty consumer reached from a processed
trace summary plus the explicit D.4 count clause.  This is still conditional
on the elimination projection of the source good event; neither its
probability nor an ordered multi-snapshot elimination theorem is claimed. -/
theorem gap_le_twenty_mul_gap_at_earlier_elimination_snapshot_of_traceSummary
    {K : Nat} [Nonempty (Fin K)]
    (state : DelayedSAPOProcessedTraceSummary K) (horizon : Nat)
    (hD4 : state.D4CountClause horizon) (hhorizon : 1 < horizon)
    (mean : Fin K -> Real) (optimal iEarlier iLater : Fin K)
    (hoptimal : forall j, mean optimal <= mean j)
    (hmeanBounds : forall j, mean j ∈ Set.Icc (0 : Real) 1)
    (hgood : (state.toConfidenceSnapshot horizon).EliminationGoodEvent mean)
    (hoptimalActive :
      optimal ∈ (state.toConfidenceSnapshot horizon).active)
    (hEarlierEliminated :
      iEarlier ∈ (state.toConfidenceSnapshot horizon).eliminated)
    (hLaterRemaining :
      iLater ∈ (state.toConfidenceSnapshot horizon).remainingActive) :
    mean iLater - mean optimal <=
      20 * (mean iEarlier - mean optimal) := by
  exact
    (state.toProcessedPrefixCountCertificate horizon hD4).gap_le_twenty_mul_gap_at_earlier_elimination_snapshot_of_countCertificate
      (state.toConfidenceSnapshot horizon) state.toProcessedPrefix horizon
        hhorizon mean optimal iEarlier iLater hoptimal hmeanBounds hgood
          hoptimalActive hEarlierEliminated hLaterRemaining

end DelayedSAPOProcessedTraceSummary

end DelayedFeedback

end BanditRLProof
