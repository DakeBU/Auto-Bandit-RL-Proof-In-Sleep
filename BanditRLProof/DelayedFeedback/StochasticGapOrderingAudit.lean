import BanditRLProof.DelayedFeedback.StochasticGoodEventAssembly

namespace BanditRLProof

namespace DelayedFeedback

/-- The scalar form of the empirical width printed in the delayed-SAPO
source, with `scale = 2 * log T` and `count = n_i(S)`.  A nonpositive count
uses the capped width `1`; this prevents Lean's totalized real division at
zero from manufacturing a zero-width observation.  Keeping the scale explicit
isolates the positive-count order issue from logarithmic side conditions. -/
noncomputable def sourceEmpiricalWidthScale (scale count : Real) : Real :=
  if count <= 0 then 1 else min 1 (Real.sqrt (scale / count))

/-- For nonnegative scale and positive counts, the source empirical width is
antitone in the count.  Thus a later state with at least as many pulls has no
larger width than an earlier prefix. -/
theorem sourceEmpiricalWidthScale_antitone
    (scale countEarlier countLater : Real)
    (hscale : 0 <= scale) (hcountEarlier : 0 < countEarlier)
    (hcount : countEarlier <= countLater) :
    sourceEmpiricalWidthScale scale countLater <=
      sourceEmpiricalWidthScale scale countEarlier := by
  have hcountLater : 0 < countLater := hcountEarlier.trans_le hcount
  rw [sourceEmpiricalWidthScale, if_neg (not_le.mpr hcountLater)]
  rw [sourceEmpiricalWidthScale, if_neg (not_le.mpr hcountEarlier)]
  apply min_le_min_left
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_left hscale hcountEarlier hcount

/-- Exact small instance used to audit the direction of the displayed D.10
prefix-to-elimination inequality. -/
@[simp]
theorem sourceEmpiricalWidthScale_one_one :
    sourceEmpiricalWidthScale 1 1 = 1 := by
  norm_num [sourceEmpiricalWidthScale]

/-- Four times the count gives half the uncapped width in the same exact
instance. -/
@[simp]
theorem sourceEmpiricalWidthScale_one_four :
    sourceEmpiricalWidthScale 1 4 = (1 / 2 : Real) := by
  norm_num [sourceEmpiricalWidthScale]

/-- The reverse inequality used in the displayed D.10 proof is not a generic
consequence of prefix count growth: it already fails at scale one between
counts one and four.  This diagnoses an edge of the frozen proof, not a
counterexample to every possible repair of Lemma D.10. -/
theorem not_sourceEmpiricalWidthScale_one_le_four :
    not (sourceEmpiricalWidthScale 1 1 <=
      sourceEmpiricalWidthScale 1 4) := by
  norm_num

/-- A literal source-width instance at integer horizon `T = 4`.  Moving from
one to four processed pulls strictly decreases the printed capped radius, so
the reverse transport fails inside the paper's own parameter domain rather
than only for the normalized scale-one diagnostic above. -/
theorem not_sourceEmpiricalWidthScale_horizon_four_one_le_four :
    ¬ (sourceEmpiricalWidthScale (2 * Real.log 4) 1 <=
      sourceEmpiricalWidthScale (2 * Real.log 4) 4) := by
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hhalfLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h ⊢
    exact h
  have hscale : (1 : Real) <= 2 * Real.log 4 := by
    rw [hlogFour]
    linarith
  have hone : sourceEmpiricalWidthScale (2 * Real.log 4) 1 = 1 := by
    rw [sourceEmpiricalWidthScale, if_neg (by norm_num : ¬ ((1 : Real) <= 0))]
    exact min_eq_left (Real.one_le_sqrt.mpr (by simpa using hscale))
  have hlogTwoNonnegative : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogTwoLtOne : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : Real) < 2) (by norm_num : (2 : Real) ≠ 1)
    norm_num at h ⊢
    exact h
  have hratio : (2 * Real.log 4) / 4 = Real.log 2 := by
    rw [hlogFour]
    ring
  have hsqrt : Real.sqrt ((2 * Real.log 4) / 4) < 1 := by
    rw [hratio, <- Real.sqrt_one]
    exact Real.sqrt_lt_sqrt hlogTwoNonnegative hlogTwoLtOne
  have hfour : sourceEmpiricalWidthScale (2 * Real.log 4) 4 < 1 := by
    rw [sourceEmpiricalWidthScale, if_neg (by norm_num : ¬ ((4 : Real) <= 0))]
    exact (min_le_right 1 _).trans_lt hsqrt
  rw [hone]
  exact not_le.mpr hfour

/-- At one source elimination snapshot, the line-7 strict test and the
elimination projection of the stochastic good event put the eliminated arm's
true gap strictly above eight empirical widths.  This is the lower endpoint
used by the repaired D.12 route below; it is derived from the actual source
snapshot rather than supplied as a scalar contract field. -/
theorem eight_mul_empiricalWidth_lt_gap_of_mem_eliminated
    {K : Nat} [Nonempty (Fin K)]
    (snapshot : DelayedSAPOSourceConfidenceSnapshot K)
    (mean : Fin K -> Real) (optimal i : Fin K)
    (hoptimal : forall j, mean optimal <= mean j)
    (hgood : snapshot.EliminationGoodEvent mean)
    (hi : i ∈ snapshot.eliminated) :
    8 * snapshot.empiricalWidth i < mean i - mean optimal := by
  have heliminated :=
    (DelayedSAPOEliminationSnapshot.mem_eliminated_iff
      snapshot.toDelayedSAPOEliminationSnapshot i).mp hi
  have hmeanUpper :
      snapshot.empiricalMean i <= mean i + snapshot.empiricalWidth i := by
    have h := (abs_le.mp (hgood.empirical_confidence i)).2
    linarith
  have hoptimalUcb : mean optimal <= snapshot.ucbStar :=
    snapshot.optimalMean_le_ucbStar_of_eliminationGoodEvent
      mean optimal hoptimal hgood
  linarith [heliminated.2]

/-- A still-active arm's gap is at most sixteen of its widths at the same
processed prefix, once the source upper-confidence surface is bounded by the
current optimal-arm empirical radius and the optimal width is within factor
three.  These are exactly the algebraic facts used inside the displayed D.10
proof; no transport to a later elimination prefix occurs here. -/
theorem gap_le_sixteen_mul_empiricalWidth_of_mem_remainingActive
    {K : Nat} [Nonempty (Fin K)]
    (snapshot : DelayedSAPOSourceConfidenceSnapshot K)
    (mean : Fin K -> Real) (optimal i : Fin K)
    (hgood : snapshot.EliminationGoodEvent mean)
    (hi : i ∈ snapshot.remainingActive)
    (hucbCurrent :
      snapshot.ucbStar <=
        snapshot.empiricalMean optimal + snapshot.empiricalWidth optimal)
    (hoptimalWidth :
      snapshot.empiricalWidth optimal <= 3 * snapshot.empiricalWidth i) :
    mean i - mean optimal <= 16 * snapshot.empiricalWidth i := by
  have hnotEliminated :=
    (DelayedSAPOEliminationSnapshot.mem_remainingActive_iff
      snapshot.toDelayedSAPOEliminationSnapshot i).mp hi
  have hmeanLower :
      mean i - snapshot.empiricalWidth i <= snapshot.empiricalMean i := by
    have h := (abs_le.mp (hgood.empirical_confidence i)).1
    linarith
  have hoptimalEmpiricalUpper :
      snapshot.empiricalMean optimal <=
        mean optimal + snapshot.empiricalWidth optimal := by
    have h := (abs_le.mp (hgood.empirical_confidence optimal)).2
    linarith
  linarith [hnotEliminated.2]

/-- Same-snapshot repair of the displayed D.12 / main-text Lemma 4.2 chain.
When `iEarlier` is eliminated and `iLater` remains active in that very update,
the active-prefix D.10 gap upper bound can be consumed before any later
elimination snapshot is mentioned.  The proof therefore avoids the reversed
prefix-to-elimination width inequality diagnosed above.  The two width
comparison premises still have to be produced by the source count event on a
recursive Delayed SAPO trajectory. -/
theorem gap_le_twenty_mul_gap_at_earlier_elimination_snapshot
    {K : Nat} [Nonempty (Fin K)]
    (snapshot : DelayedSAPOSourceConfidenceSnapshot K)
    (mean : Fin K -> Real) (optimal iEarlier iLater : Fin K)
    (hoptimal : forall j, mean optimal <= mean j)
    (hgood : snapshot.EliminationGoodEvent mean)
    (hEarlierEliminated : iEarlier ∈ snapshot.eliminated)
    (hLaterRemaining : iLater ∈ snapshot.remainingActive)
    (hucbCurrent :
      snapshot.ucbStar <=
        snapshot.empiricalMean optimal + snapshot.empiricalWidth optimal)
    (hoptimalWidth :
      snapshot.empiricalWidth optimal <=
        3 * snapshot.empiricalWidth iLater)
    (hpairWidth :
      snapshot.empiricalWidth iLater <=
        10 * snapshot.empiricalWidth iEarlier) :
    mean iLater - mean optimal <=
      20 * (mean iEarlier - mean optimal) := by
  have hlater := gap_le_sixteen_mul_empiricalWidth_of_mem_remainingActive
    snapshot mean optimal iLater hgood hLaterRemaining hucbCurrent hoptimalWidth
  have hearlier := eight_mul_empiricalWidth_lt_gap_of_mem_eliminated
    snapshot mean optimal iEarlier hoptimal hgood hEarlierEliminated
  linarith

/-- Exact deterministic interface needed by the displayed proof of source
Lemma D.12 (main-text Lemma 4.2).  Its index is a shared processed-sequence
prefix length, not wall-clock action time.  The fields deliberately name the
four edges consumed by D.12: D.10 supplies the gap endpoints and cross-arm
comparison, while the width definition supplies the time transport. -/
structure DelayedSAPOD10D12GapOrderingContract (K : Nat) where
  eliminationPrefixIndex : Fin K -> Nat
  widthAt : Fin K -> Nat -> Real
  gap : Fin K -> Real
  gap_upper_at_elimination : forall i,
    gap i <= 16 * widthAt i (eliminationPrefixIndex i)
  surrogateGap_lower_at_elimination : forall i,
    8 * widthAt i (eliminationPrefixIndex i) <= gap i
  width_antitone : forall i {earlier later}, earlier <= later ->
    widthAt i later <= widthAt i earlier
  width_comparable_before_both : forall i j t,
    t <= eliminationPrefixIndex i -> t <= eliminationPrefixIndex j ->
      widthAt i t <= 10 * widthAt j t

namespace DelayedSAPOD10D12GapOrderingContract

/-- The source surrogate gap `Delta-tilde_i = 8 width_i(S-tilde_i)`. -/
noncomputable def surrogateGap {K : Nat}
    (contract : DelayedSAPOD10D12GapOrderingContract K)
    (i : Fin K) : Real :=
  8 * contract.widthAt i (contract.eliminationPrefixIndex i)

/-- Lower half of the displayed D.10 two-sided surrogate-gap comparison. -/
theorem surrogateGap_le_gap {K : Nat}
    (contract : DelayedSAPOD10D12GapOrderingContract K)
    (i : Fin K) :
    contract.surrogateGap i <= contract.gap i := by
  exact contract.surrogateGap_lower_at_elimination i

/-- Upper half of the displayed D.10 two-sided comparison, exposed from the
factor-16 endpoint rather than assumed in factor-two form. -/
theorem gap_le_two_mul_surrogateGap {K : Nat}
    (contract : DelayedSAPOD10D12GapOrderingContract K)
    (i : Fin K) :
    contract.gap i <= 2 * contract.surrogateGap i := by
  have h := contract.gap_upper_at_elimination i
  dsimp [surrogateGap]
  linarith

/-- The four inequalities in the source's displayed D.12 chain, kept
separate so an audit can identify which edge is missing from a recursive
Delayed SAPO implementation. -/
theorem d12_gap_ordering_chain {K : Nat}
    (contract : DelayedSAPOD10D12GapOrderingContract K)
    (iEarlier iLater : Fin K)
    (horder : contract.eliminationPrefixIndex iEarlier <=
      contract.eliminationPrefixIndex iLater) :
    contract.gap iLater <=
        16 * contract.widthAt iLater (contract.eliminationPrefixIndex iLater) /\
      16 * contract.widthAt iLater (contract.eliminationPrefixIndex iLater) <=
        16 * contract.widthAt iLater (contract.eliminationPrefixIndex iEarlier) /\
      16 * contract.widthAt iLater (contract.eliminationPrefixIndex iEarlier) <=
        160 * contract.widthAt iEarlier (contract.eliminationPrefixIndex iEarlier) /\
      160 * contract.widthAt iEarlier (contract.eliminationPrefixIndex iEarlier) <=
        20 * contract.gap iEarlier := by
  have hgapLater := contract.gap_upper_at_elimination iLater
  have htime := contract.width_antitone iLater horder
  have hcompare := contract.width_comparable_before_both
    iLater iEarlier (contract.eliminationPrefixIndex iEarlier) horder le_rfl
  have hgapEarlier := contract.surrogateGap_lower_at_elimination iEarlier
  constructor
  · exact hgapLater
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Conditional source Lemma D.12 / main-text Lemma 4.2 consumer.  It proves
the factor-20 gap ordering once the exact D.10 endpoints and the correctly
oriented width transport are supplied; it does not claim those disputed
inputs follow from the current one-snapshot library. -/
theorem gap_le_twenty_mul_gap_of_eliminationPrefixIndex_le {K : Nat}
    (contract : DelayedSAPOD10D12GapOrderingContract K)
    (iEarlier iLater : Fin K)
    (horder : contract.eliminationPrefixIndex iEarlier <=
      contract.eliminationPrefixIndex iLater) :
    contract.gap iLater <= 20 * contract.gap iEarlier := by
  rcases contract.d12_gap_ordering_chain iEarlier iLater horder with
    ⟨h1, h2, h3, h4⟩
  exact h1.trans (h2.trans (h3.trans h4))

end DelayedSAPOD10D12GapOrderingContract

end DelayedFeedback

end BanditRLProof
