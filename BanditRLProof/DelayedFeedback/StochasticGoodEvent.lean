import BanditRLProof.DelayedFeedback.Elimination
import BanditRLProof.ProbabilityUnionBound

namespace BanditRLProof

namespace DelayedFeedback

open MeasureTheory

/-- The two armwise upper-confidence surfaces entering the source definition
of `ucbStar`.  The recursive construction of those surfaces from a processed
history remains outside this snapshot. -/
structure DelayedSAPOSourceConfidenceSnapshot (K : Nat) extends
    DelayedSAPOEliminationSnapshot K where
  empiricalUpper : Fin K → ℝ
  importanceUpper : Fin K → ℝ

namespace DelayedSAPOSourceConfidenceSnapshot

/-- Source-shaped projection of
`ucbStar(S) = min_i {ucb_i(S), overline-ucb_i(S)}`. -/
noncomputable def sourceUcbStar {K : Nat} [Nonempty (Fin K)]
    (snapshot : DelayedSAPOSourceConfidenceSnapshot K) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i =>
    min (snapshot.empiricalUpper i) (snapshot.importanceUpper i))

/-- The elimination-relevant projection of the stochastic good event in
Definition D.1.  It records both empirical-mean confidence and the two upper
confidence surfaces used by `ucbStar`.  Count/phase/error/delay clauses from
the full source event are deliberately not included here. -/
structure EliminationGoodEvent {K : Nat} [Nonempty (Fin K)]
    (snapshot : DelayedSAPOSourceConfidenceSnapshot K)
    (mean : Fin K → ℝ) : Prop where
  width_nonnegative : ∀ i, 0 ≤ snapshot.empiricalWidth i
  empirical_confidence : ∀ i,
    |snapshot.empiricalMean i - mean i| ≤ snapshot.empiricalWidth i
  empiricalUpper_confidence : ∀ i, mean i ≤ snapshot.empiricalUpper i
  importanceUpper_confidence : ∀ i, mean i ≤ snapshot.importanceUpper i
  ucbStar_eq_source : snapshot.ucbStar = snapshot.sourceUcbStar

/-- On the source-shaped elimination good event, the best loss mean is below
the exact minimum of both armwise upper-confidence surfaces. -/
theorem optimalMean_le_ucbStar_of_eliminationGoodEvent
    {K : Nat} [Nonempty (Fin K)]
    (snapshot : DelayedSAPOSourceConfidenceSnapshot K)
    (mean : Fin K → ℝ) (optimal : Fin K)
    (hoptimal : ∀ i, mean optimal ≤ mean i)
    (hgood : EliminationGoodEvent snapshot mean) :
    mean optimal ≤ snapshot.ucbStar := by
  rw [hgood.ucbStar_eq_source, sourceUcbStar]
  apply Finset.le_inf' Finset.univ_nonempty
  intro i _hi
  exact le_trans (hoptimal i)
    (le_min (hgood.empiricalUpper_confidence i)
      (hgood.importanceUpper_confidence i))

/-- The source-shaped elimination projection constructs the exact certificate
consumed by the deterministic core of Lemma D.9; no independent
`mean optimal <= ucbStar` premise remains. -/
theorem optimalArmSurvivalCertificate_of_eliminationGoodEvent
    {K : Nat} [Nonempty (Fin K)]
    (snapshot : DelayedSAPOSourceConfidenceSnapshot K)
    (mean : Fin K → ℝ) (optimal : Fin K)
    (hoptimal : ∀ i, mean optimal ≤ mean i)
    (hactive : optimal ∈ snapshot.active)
    (hgood : EliminationGoodEvent snapshot mean) :
    DelayedSAPOEliminationSnapshot.OptimalArmSurvivalCertificate
      snapshot.toDelayedSAPOEliminationSnapshot mean optimal where
  optimal_active := hactive
  width_nonnegative := hgood.width_nonnegative optimal
  empirical_confidence := hgood.empirical_confidence optimal
  optimalMean_le_ucbStar :=
    optimalMean_le_ucbStar_of_eliminationGoodEvent
      snapshot mean optimal hoptimal hgood

/-- Source Lemma D.9 at one elimination snapshot, conditional only on the
elimination projection of Definition D.1 and current activity of the optimal
arm.  Establishing the full good-event probability and persistence over the
recursive state machine remain separate obligations. -/
theorem optimal_mem_remainingActive_of_eliminationGoodEvent
    {K : Nat} [Nonempty (Fin K)]
    (snapshot : DelayedSAPOSourceConfidenceSnapshot K)
    (mean : Fin K → ℝ) (optimal : Fin K)
    (hoptimal : ∀ i, mean optimal ≤ mean i)
    (hactive : optimal ∈ snapshot.active)
    (hgood : EliminationGoodEvent snapshot mean) :
    optimal ∈ snapshot.remainingActive := by
  exact DelayedSAPOEliminationSnapshot.optimal_mem_remainingActive_of_certificate
    snapshot.toDelayedSAPOEliminationSnapshot mean optimal
    (optimalArmSurvivalCertificate_of_eliminationGoodEvent
      snapshot mean optimal hoptimal hactive hgood)

/-- Random-state event on which the elimination projection of Definition D.1
holds. -/
def eliminationGoodEventSet {Ω : Type*} {K : Nat} [Nonempty (Fin K)]
    (snapshot : Ω → DelayedSAPOSourceConfidenceSnapshot K)
    (mean : Fin K → ℝ) : Set Ω :=
  {ω | EliminationGoodEvent (snapshot ω) mean}

/-- Event that the optimal arm survives the current elimination update. -/
def optimalSurvivalEventSet {Ω : Type*} {K : Nat}
    (snapshot : Ω → DelayedSAPOSourceConfidenceSnapshot K)
    (optimal : Fin K) : Set Ω :=
  {ω | optimal ∈ (snapshot ω).remainingActive}

/-- The elimination good event is contained in the optimal-arm survival event
when the optimal arm is active in every input snapshot. -/
theorem eliminationGoodEventSet_subset_optimalSurvivalEventSet
    {Ω : Type*} {K : Nat} [Nonempty (Fin K)]
    (snapshot : Ω → DelayedSAPOSourceConfidenceSnapshot K)
    (mean : Fin K → ℝ) (optimal : Fin K)
    (hoptimal : ∀ i, mean optimal ≤ mean i)
    (hactive : ∀ ω, optimal ∈ (snapshot ω).active) :
    eliminationGoodEventSet snapshot mean ⊆
      optimalSurvivalEventSet snapshot optimal := by
  intro ω hgood
  exact optimal_mem_remainingActive_of_eliminationGoodEvent
    (snapshot ω) mean optimal hoptimal (hactive ω) hgood

/-- Any tail bound for the complement of the source-shaped good event
immediately controls the probability that the optimal arm is eliminated. -/
theorem measure_optimalSurvivalEventSet_compl_le
    {Ω : Type*} [MeasurableSpace Ω] {K : Nat} [Nonempty (Fin K)]
    (mu : Measure Ω)
    (snapshot : Ω → DelayedSAPOSourceConfidenceSnapshot K)
    (mean : Fin K → ℝ) (optimal : Fin K)
    (hoptimal : ∀ i, mean optimal ≤ mean i)
    (hactive : ∀ ω, optimal ∈ (snapshot ω).active) :
    mu (optimalSurvivalEventSet snapshot optimal)ᶜ ≤
      mu (eliminationGoodEventSet snapshot mean)ᶜ := by
  apply measure_mono
  intro ω hfailure hgood
  exact hfailure
    (eliminationGoodEventSet_subset_optimalSurvivalEventSet
      snapshot mean optimal hoptimal hactive hgood)

/-- Failure-budget consumer for the D.9 projection.  The hypothesis must be
discharged by the D.2--D.8 concentration/counting development; this theorem
does not manufacture that probability estimate. -/
theorem measure_optimalSurvivalEventSet_compl_le_of_goodEvent
    {Ω : Type*} [MeasurableSpace Ω] {K : Nat} [Nonempty (Fin K)]
    (mu : Measure Ω)
    (snapshot : Ω → DelayedSAPOSourceConfidenceSnapshot K)
    (mean : Fin K → ℝ) (optimal : Fin K)
    (delta : ℝ)
    (hoptimal : ∀ i, mean optimal ≤ mean i)
    (hactive : ∀ ω, optimal ∈ (snapshot ω).active)
    (hgoodProbability :
      mu (eliminationGoodEventSet snapshot mean)ᶜ ≤ ENNReal.ofReal delta) :
    mu (optimalSurvivalEventSet snapshot optimal)ᶜ ≤ ENNReal.ofReal delta := by
  exact (measure_optimalSurvivalEventSet_compl_le
    mu snapshot mean optimal hoptimal hactive).trans hgoodProbability

end DelayedSAPOSourceConfidenceSnapshot

end DelayedFeedback

end BanditRLProof
