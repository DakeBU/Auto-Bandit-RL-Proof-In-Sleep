import BanditRLProof.DelayedFeedback.StochasticGapOrderingAudit

namespace BanditRLProof

namespace DelayedFeedback

open scoped BigOperators

/-- A ledger for one ordered ledger of source rounds whose feedback has been
processed by delayed SAPO.  Each entry stores the arm chosen at that source
round and the Algorithm-5 allocation that was in force when the action was
sampled.  In particular, `inactiveProbabilityAtSource` is source-time data;
it must not be reconstructed from the later processing-time state. -/
structure DelayedSAPOProcessedPrefix (K : Nat) where
  length : Nat
  activeAtSource : Fin length -> Finset (Fin K)
  inactiveProbabilityAtSource : Fin length -> Fin K -> Real
  chosenArmAtSource : Fin length -> Fin K
  previousEmpiricalUpper : Fin K -> Real

namespace DelayedSAPOProcessedPrefix

/-- The source count `n_i(S)` on the processed ledger. -/
def processedPullCount {K : Nat}
    (ledger : DelayedSAPOProcessedPrefix K) (i : Fin K) : Nat :=
  (Finset.univ.filter fun s => ledger.chosenArmAtSource s = i).card

/-- The source conditional mass `sum_{s in S} p_i(s)` on the same ledger. -/
noncomputable def expectedPullMass {K : Nat}
    (ledger : DelayedSAPOProcessedPrefix K) (i : Fin K) : Real :=
  ∑ s, delayedSAPOProbability (ledger.activeAtSource s)
    (ledger.inactiveProbabilityAtSource s) i

/-- Two arms that were active at every source round represented by the
processed ledger receive the same cumulative Algorithm-5 probability mass.
This is the deterministic line-15 producer used by the D.1 count clause. -/
theorem expectedPullMass_eq_of_active_throughout
    {K : Nat} (ledger : DelayedSAPOProcessedPrefix K) (i j : Fin K)
    (hi : forall s, i ∈ ledger.activeAtSource s)
    (hj : forall s, j ∈ ledger.activeAtSource s) :
    ledger.expectedPullMass i = ledger.expectedPullMass j := by
  classical
  apply Finset.sum_congr rfl
  intro s _hs
  rw [delayedSAPOProbability_of_active
      (ledger.activeAtSource s) (ledger.inactiveProbabilityAtSource s) (hi s)]
  rw [delayedSAPOProbability_of_active
      (ledger.activeAtSource s) (ledger.inactiveProbabilityAtSource s) (hj s)]

end DelayedSAPOProcessedPrefix

/-- The exact deterministic projection needed from Algorithm 5 and the
pull-count clause of source Definition D.1 at one processed ledger.

The certificate keeps the source-time allocation ledger explicit.  It assumes
the D.1 count inequalities and the source definitions of the width and the
recursive empirical UCB, but it does not assume either of the width-comparison
conclusions that it is designed to prove.  Constructing this projection from
the full recursive delayed-SAPO state and proving its probability are separate
obligations. -/
structure DelayedSAPOProcessedPrefixCountCertificate
    {K : Nat} [Nonempty (Fin K)]
    (snapshot : DelayedSAPOSourceConfidenceSnapshot K)
    (ledger : DelayedSAPOProcessedPrefix K) (horizon : Nat) : Prop where
  active_persistence : forall s,
    snapshot.active ⊆ ledger.activeAtSource s
  count_lower : forall i,
    (1 / 2 : Real) * ledger.expectedPullMass i -
        3 * Real.log (horizon : Real) <=
      (ledger.processedPullCount i : Real)
  count_upper : forall i,
    (ledger.processedPullCount i : Real) <=
      2 * ledger.expectedPullMass i + 12 * Real.log (horizon : Real)
  empiricalWidth_eq_source : forall i,
    snapshot.empiricalWidth i =
      sourceEmpiricalWidthScale (2 * Real.log (horizon : Real))
        (ledger.processedPullCount i : Real)
  empiricalUpper_eq_source : forall i,
    snapshot.empiricalUpper i =
      min (snapshot.empiricalMean i + snapshot.empiricalWidth i)
        (ledger.previousEmpiricalUpper i)

namespace DelayedSAPOProcessedPrefixCountCertificate

/-- The capped source empirical width is always nonnegative. -/
theorem sourceEmpiricalWidthScale_nonneg (scale count : Real) :
    0 <= sourceEmpiricalWidthScale scale count := by
  by_cases hcount : count <= 0
  · simp [sourceEmpiricalWidthScale, hcount]
  · rw [sourceEmpiricalWidthScale, if_neg hcount]
    exact le_min (by norm_num) (Real.sqrt_nonneg _)

/-- The capped source empirical width is at most one. -/
theorem sourceEmpiricalWidthScale_le_one (scale count : Real) :
    sourceEmpiricalWidthScale scale count <= 1 := by
  by_cases hcount : count <= 0
  · simp [sourceEmpiricalWidthScale, hcount]
  · rw [sourceEmpiricalWidthScale, if_neg hcount]
    exact min_le_left _ _

/-- If one positive count is at most eight times another, then the other arm's
inverse-square-root width is at most three times the reference width.  The
factor three is the integer relaxation of `sqrt 8` used in source D.10. -/
theorem sourceEmpiricalWidthScale_le_three_of_count_le_eight_mul
    (scale countReference countOther : Real)
    (hscale : 0 <= scale) (hreference : 0 < countReference)
    (hcount : countReference <= 8 * countOther) :
    sourceEmpiricalWidthScale scale countOther <=
      3 * sourceEmpiricalWidthScale scale countReference := by
  have hother : 0 < countOther := by nlinarith
  rw [sourceEmpiricalWidthScale, if_neg (not_le.mpr hother)]
  rw [sourceEmpiricalWidthScale, if_neg (not_le.mpr hreference)]
  have hratio :
      scale / countOther <= 9 * (scale / countReference) := by
    rw [show 9 * (scale / countReference) =
      (9 * scale) / countReference by ring]
    rw [div_le_div_iff₀ hother hreference]
    have hscaled :
        scale * countReference <= scale * (8 * countOther) :=
      mul_le_mul_of_nonneg_left hcount hscale
    have hscaleOther : 0 <= scale * countOther :=
      mul_nonneg hscale hother.le
    nlinarith
  have hreferenceRatio : 0 <= scale / countReference :=
    div_nonneg hscale hreference.le
  have hotherRatio : 0 <= scale / countOther :=
    div_nonneg hscale hother.le
  have hsqrt :
      Real.sqrt (scale / countOther) <=
        3 * Real.sqrt (scale / countReference) := by
    have hotherSquare := Real.sq_sqrt hotherRatio
    have hreferenceSquare := Real.sq_sqrt hreferenceRatio
    have hotherSqrtNonnegative := Real.sqrt_nonneg (scale / countOther)
    have hreferenceSqrtNonnegative :=
      Real.sqrt_nonneg (scale / countReference)
    nlinarith
  by_cases hcapped : 1 <= Real.sqrt (scale / countReference)
  · rw [min_eq_left hcapped]
    calc
      min 1 (Real.sqrt (scale / countOther)) <= 1 := min_le_left _ _
      _ <= 3 * 1 := by norm_num
  · have huncapped : Real.sqrt (scale / countReference) <= 1 :=
      (le_of_lt (lt_of_not_ge hcapped))
    rw [min_eq_right huncapped]
    exact (min_le_right 1 _).trans hsqrt

/-- Active arms have equal source-time expected pull mass on the ledger. -/
theorem expectedPullMass_eq_of_mem_active
    {K : Nat} [Nonempty (Fin K)]
    {snapshot : DelayedSAPOSourceConfidenceSnapshot K}
    {ledger : DelayedSAPOProcessedPrefix K} {horizon : Nat}
    (certificate : DelayedSAPOProcessedPrefixCountCertificate
      snapshot ledger horizon)
    {i j : Fin K} (hi : i ∈ snapshot.active) (hj : j ∈ snapshot.active) :
    ledger.expectedPullMass i = ledger.expectedPullMass j := by
  apply ledger.expectedPullMass_eq_of_active_throughout
  · intro s
    exact certificate.active_persistence s hi
  · intro s
    exact certificate.active_persistence s hj

/-- Combining the two exact D.1 count inequalities with equal active-arm
probability mass gives the stronger `n_j >= n_i/4 - 6 log T` comparison. -/
theorem quarter_count_sub_six_log_le_count_of_mem_active
    {K : Nat} [Nonempty (Fin K)]
    {snapshot : DelayedSAPOSourceConfidenceSnapshot K}
    {ledger : DelayedSAPOProcessedPrefix K} {horizon : Nat}
    (certificate : DelayedSAPOProcessedPrefixCountCertificate
      snapshot ledger horizon)
    {i j : Fin K} (hi : i ∈ snapshot.active) (hj : j ∈ snapshot.active) :
    (ledger.processedPullCount i : Real) / 4 -
        6 * Real.log (horizon : Real) <=
      (ledger.processedPullCount j : Real) := by
  have hequal := certificate.expectedPullMass_eq_of_mem_active hi hj
  have hiUpper := certificate.count_upper i
  have hjLower := certificate.count_lower j
  linarith

/-- In the source large-count branch, any other active arm has at least one
eighth of the reference arm's processed count. -/
theorem eighth_count_le_count_of_large_count
    {K : Nat} [Nonempty (Fin K)]
    {snapshot : DelayedSAPOSourceConfidenceSnapshot K}
    {ledger : DelayedSAPOProcessedPrefix K} {horizon : Nat}
    (certificate : DelayedSAPOProcessedPrefixCountCertificate
      snapshot ledger horizon)
    (hhorizon : 1 < horizon) {i j : Fin K}
    (hi : i ∈ snapshot.active) (hj : j ∈ snapshot.active)
    (hlarge : 192 * Real.log (horizon : Real) <
      (ledger.processedPullCount i : Real)) :
    (ledger.processedPullCount i : Real) / 8 <=
      (ledger.processedPullCount j : Real) := by
  have hquarter :=
    certificate.quarter_count_sub_six_log_le_count_of_mem_active hi hj
  have hhorizonReal : (1 : Real) < (horizon : Real) := by exact_mod_cast hhorizon
  have hlog : 0 < Real.log (horizon : Real) := Real.log_pos hhorizonReal
  nlinarith

/-- The source D.10 factor-three width producer in the large-count branch. -/
theorem empiricalWidth_le_three_of_large_count
    {K : Nat} [Nonempty (Fin K)]
    {snapshot : DelayedSAPOSourceConfidenceSnapshot K}
    {ledger : DelayedSAPOProcessedPrefix K} {horizon : Nat}
    (certificate : DelayedSAPOProcessedPrefixCountCertificate
      snapshot ledger horizon)
    (hhorizon : 1 < horizon) {iReference iOther : Fin K}
    (hreferenceActive : iReference ∈ snapshot.active)
    (hotherActive : iOther ∈ snapshot.active)
    (hlarge : 192 * Real.log (horizon : Real) <
      (ledger.processedPullCount iReference : Real)) :
    snapshot.empiricalWidth iOther <=
      3 * snapshot.empiricalWidth iReference := by
  have hhorizonReal : (1 : Real) < (horizon : Real) := by exact_mod_cast hhorizon
  have hlog : 0 < Real.log (horizon : Real) := Real.log_pos hhorizonReal
  have hcountEighth := certificate.eighth_count_le_count_of_large_count
    hhorizon hreferenceActive hotherActive hlarge
  have hreferencePositive :
      0 < (ledger.processedPullCount iReference : Real) := by
    nlinarith
  rw [certificate.empiricalWidth_eq_source iOther,
    certificate.empiricalWidth_eq_source iReference]
  apply sourceEmpiricalWidthScale_le_three_of_count_le_eight_mul
  · linarith
  · exact hreferencePositive
  · nlinarith

/-- The unconditional same-ledger D.10 width comparison.  It is derived from
the source-time allocation ledger, the D.1 count event, and the exact source
width formula; no factor-ten comparison is assumed as a contract field. -/
theorem empiricalWidth_le_ten_of_mem_active
    {K : Nat} [Nonempty (Fin K)]
    {snapshot : DelayedSAPOSourceConfidenceSnapshot K}
    {ledger : DelayedSAPOProcessedPrefix K} {horizon : Nat}
    (certificate : DelayedSAPOProcessedPrefixCountCertificate
      snapshot ledger horizon)
    (hhorizon : 1 < horizon) {iReference iOther : Fin K}
    (hreferenceActive : iReference ∈ snapshot.active)
    (hotherActive : iOther ∈ snapshot.active) :
    snapshot.empiricalWidth iOther <=
      10 * snapshot.empiricalWidth iReference := by
  have hhorizonReal : (1 : Real) < (horizon : Real) := by exact_mod_cast hhorizon
  have hlog : 0 < Real.log (horizon : Real) := Real.log_pos hhorizonReal
  by_cases hsmall :
      (ledger.processedPullCount iReference : Real) <=
        192 * Real.log (horizon : Real)
  · have hreferenceWidth :
        1 <= 10 * snapshot.empiricalWidth iReference := by
      rw [certificate.empiricalWidth_eq_source iReference]
      exact one_le_ten_mul_sourceEmpiricalWidthScale_two_log_of_small_count
        (horizon : Real) (ledger.processedPullCount iReference : Real)
        hhorizonReal hsmall
    have hotherWidth : snapshot.empiricalWidth iOther <= 1 := by
      rw [certificate.empiricalWidth_eq_source iOther]
      exact sourceEmpiricalWidthScale_le_one _ _
    linarith
  · have hthree := certificate.empiricalWidth_le_three_of_large_count
      hhorizon hreferenceActive hotherActive (lt_of_not_ge hsmall)
    have hreferenceNonnegative : 0 <= snapshot.empiricalWidth iReference := by
      rw [certificate.empiricalWidth_eq_source iReference]
      exact sourceEmpiricalWidthScale_nonneg _ _
    linarith

/-- The recursive empirical UCB is no larger than the current empirical
mean-plus-width surface, so the source minimum `ucbStar` has the current-UCB
upper edge needed by the active-arm gap proof. -/
theorem ucbStar_le_empiricalMean_add_width
    {K : Nat} [Nonempty (Fin K)]
    {snapshot : DelayedSAPOSourceConfidenceSnapshot K}
    {ledger : DelayedSAPOProcessedPrefix K} {horizon : Nat}
    (certificate : DelayedSAPOProcessedPrefixCountCertificate
      snapshot ledger horizon)
    (mean : Fin K -> Real)
    (hgood : snapshot.EliminationGoodEvent mean) (i : Fin K) :
    snapshot.ucbStar <=
      snapshot.empiricalMean i + snapshot.empiricalWidth i := by
  rw [hgood.ucbStar_eq_source, DelayedSAPOSourceConfidenceSnapshot.sourceUcbStar]
  calc
    Finset.univ.inf' Finset.univ_nonempty (fun j =>
        min (snapshot.empiricalUpper j) (snapshot.importanceUpper j)) <=
        min (snapshot.empiricalUpper i) (snapshot.importanceUpper i) :=
      Finset.inf'_le _ (Finset.mem_univ i)
    _ <= snapshot.empiricalUpper i := min_le_left _ _
    _ <= snapshot.empiricalMean i + snapshot.empiricalWidth i := by
      rw [certificate.empiricalUpper_eq_source i]
      exact min_le_left _ _

/-- The exact large/small branch expected by the existing active-arm gap
consumer is now produced from the processed-ledger certificate. -/
theorem activeArmGapBranch
    {K : Nat} [Nonempty (Fin K)]
    {snapshot : DelayedSAPOSourceConfidenceSnapshot K}
    {ledger : DelayedSAPOProcessedPrefix K} {horizon : Nat}
    (certificate : DelayedSAPOProcessedPrefixCountCertificate
      snapshot ledger horizon)
    (hhorizon : 1 < horizon) (mean : Fin K -> Real)
    (hgood : snapshot.EliminationGoodEvent mean)
    {optimal i : Fin K} (hoptimalActive : optimal ∈ snapshot.active)
    (hiActive : i ∈ snapshot.active) :
    (snapshot.ucbStar <=
          snapshot.empiricalMean optimal + snapshot.empiricalWidth optimal /\
        snapshot.empiricalWidth optimal <=
          3 * snapshot.empiricalWidth i) \/
      (exists scale count : Real,
        0 < scale /\ count <= 96 * scale /\
        snapshot.empiricalWidth i =
          sourceEmpiricalWidthScale scale count) := by
  have hhorizonReal : (1 : Real) < (horizon : Real) := by exact_mod_cast hhorizon
  have hlog : 0 < Real.log (horizon : Real) := Real.log_pos hhorizonReal
  by_cases hsmall :
      (ledger.processedPullCount i : Real) <=
        192 * Real.log (horizon : Real)
  · right
    refine ⟨2 * Real.log (horizon : Real),
      (ledger.processedPullCount i : Real), ?_, ?_, ?_⟩
    · linarith
    · nlinarith
    · exact certificate.empiricalWidth_eq_source i
  · left
    constructor
    · exact certificate.ucbStar_le_empiricalMean_add_width mean hgood optimal
    · exact certificate.empiricalWidth_le_three_of_large_count
        hhorizon hiActive hoptimalActive (lt_of_not_ge hsmall)

/-- Repaired same-snapshot D.12 / main-text Lemma-4.2 deterministic slice.
The theorem removes the manually supplied branch and pair-width premises
from the earlier consumer: both are generated by the actual Algorithm-5
source-time allocation ledger and the D.1 count clause.  The full recursive
state projection and probability of the source good event remain open. -/
theorem gap_le_twenty_mul_gap_at_earlier_elimination_snapshot_of_countCertificate
    {K : Nat} [Nonempty (Fin K)]
    (snapshot : DelayedSAPOSourceConfidenceSnapshot K)
    (ledger : DelayedSAPOProcessedPrefix K) (horizon : Nat)
    (certificate : DelayedSAPOProcessedPrefixCountCertificate
      snapshot ledger horizon)
    (hhorizon : 1 < horizon)
    (mean : Fin K -> Real) (optimal iEarlier iLater : Fin K)
    (hoptimal : forall j, mean optimal <= mean j)
    (hmeanBounds : forall j, mean j ∈ Set.Icc (0 : Real) 1)
    (hgood : snapshot.EliminationGoodEvent mean)
    (hoptimalActive : optimal ∈ snapshot.active)
    (hEarlierEliminated : iEarlier ∈ snapshot.eliminated)
    (hLaterRemaining : iLater ∈ snapshot.remainingActive) :
    mean iLater - mean optimal <=
      20 * (mean iEarlier - mean optimal) := by
  have hEarlierActive : iEarlier ∈ snapshot.active :=
    (DelayedSAPOEliminationSnapshot.mem_eliminated_iff
      snapshot.toDelayedSAPOEliminationSnapshot iEarlier).mp
        hEarlierEliminated |>.1
  have hLaterActive : iLater ∈ snapshot.active :=
    (DelayedSAPOEliminationSnapshot.mem_remainingActive_iff
      snapshot.toDelayedSAPOEliminationSnapshot iLater).mp
        hLaterRemaining |>.1
  have producedBranch := certificate.activeArmGapBranch
    hhorizon mean hgood hoptimalActive hLaterActive
  have producedPairWidth := certificate.empiricalWidth_le_ten_of_mem_active
    hhorizon hEarlierActive hLaterActive
  exact gap_le_twenty_mul_gap_at_earlier_elimination_snapshot_of_large_or_small_count
    snapshot mean optimal iEarlier iLater hoptimal hmeanBounds hgood
      hEarlierEliminated hLaterRemaining producedBranch producedPairWidth

end DelayedSAPOProcessedPrefixCountCertificate

end DelayedFeedback

end BanditRLProof
