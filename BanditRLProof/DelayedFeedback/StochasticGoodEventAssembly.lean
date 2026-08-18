import BanditRLProof.DelayedFeedback.StochasticGoodEvent
import BanditRLProof.ProbabilityUnionBound

namespace BanditRLProof

namespace DelayedFeedback

open MeasureTheory

/-- The six source components combined by Corollary D.8.  These constructors
name the failure events proved separately in Lemmas D.2--D.7; they do not
assert those concentration results. -/
inductive DelayedSAPOGoodEventComponent where
  | bscConfidence
  | eapConfidence
  | pullCount
  | eliminatedDelay
  | lossDifference
  | stochasticDelay
  deriving DecidableEq, Fintype

/-- Failure-event family corresponding to the six clauses combined in source
Corollary D.8.  The stochastic-delay component may be set to the empty event
when only the oblivious-delay version is used. -/
structure DelayedSAPOGoodEventFailureFamily (Omega : Type*) where
  bscConfidence : Set Omega
  eapConfidence : Set Omega
  pullCount : Set Omega
  eliminatedDelay : Set Omega
  lossDifference : Set Omega
  stochasticDelay : Set Omega

namespace DelayedSAPOGoodEventFailureFamily

/-- Select the failure event named by a source good-event component. -/
def componentFailure {Omega : Type*}
    (family : DelayedSAPOGoodEventFailureFamily Omega) :
    DelayedSAPOGoodEventComponent -> Set Omega
  | .bscConfidence => family.bscConfidence
  | .eapConfidence => family.eapConfidence
  | .pullCount => family.pullCount
  | .eliminatedDelay => family.eliminatedDelay
  | .lossDifference => family.lossDifference
  | .stochasticDelay => family.stochasticDelay

/-- The bad event appearing in the union-bound proof of Corollary D.8. -/
def failureSet {Omega : Type*}
    (family : DelayedSAPOGoodEventFailureFamily Omega) : Set Omega :=
  ⋃ component, family.componentFailure component

/-- Source good event assembled from the complements of the six D.2--D.7
failure events. -/
def sourceGoodEventSet {Omega : Type*}
    (family : DelayedSAPOGoodEventFailureFamily Omega) : Set Omega :=
  family.failureSetᶜ

/-- The complement of the assembled source good event is exactly the union of
the six named failure events. -/
theorem sourceGoodEventSet_compl {Omega : Type*}
    (family : DelayedSAPOGoodEventFailureFamily Omega) :
    family.sourceGoodEventSetᶜ = family.failureSet := by
  simp [sourceGoodEventSet]

/-- Finite outer-measure union bound for the six D.2--D.7 components. -/
theorem measure_sourceGoodEventSet_compl_le_sum
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (family : DelayedSAPOGoodEventFailureFamily Omega) :
    mu family.sourceGoodEventSetᶜ <=
      (Finset.univ : Finset DelayedSAPOGoodEventComponent).sum
        (fun component => mu (family.componentFailure component)) := by
  rw [family.sourceGoodEventSet_compl]
  exact ProbabilityUnionBound.measure_iUnion_fintype_le_sum
    mu family.componentFailure

/-- The source `1 / T^2` budget used for Lemmas D.2--D.4. -/
noncomputable def quadraticFailureBudget (horizon : Nat) : Real :=
  (1 / (horizon : Real)) ^ 2

/-- The source `1 / T` budget used for Lemmas D.5--D.7. -/
noncomputable def linearFailureBudget (horizon : Nat) : Real :=
  1 / (horizon : Real)

/-- For a nonzero horizon, every quadratic source share is bounded by its
linear relaxation. -/
theorem quadraticFailureBudget_le_linearFailureBudget
    (horizon : Nat) (hhorizon : 0 < horizon) :
    quadraticFailureBudget horizon <= linearFailureBudget horizon := by
  let x : Real := 1 / (horizon : Real)
  have hhorizonReal : 1 <= (horizon : Real) := by
    exact_mod_cast hhorizon
  have hx_nonneg : 0 <= x := by
    dsimp [x]
    positivity
  have hx_le_one : x <= 1 := by
    dsimp [x]
    exact (div_le_one (by positivity)).2 hhorizonReal
  have hproduct : 0 <= x * (1 - x) :=
    mul_nonneg hx_nonneg (sub_nonneg.mpr hx_le_one)
  dsimp [quadraticFailureBudget, linearFailureBudget, x] at *
  nlinarith

/-- Corollary-D.8 union assembly.  The six hypotheses are precisely the
probability-producing obligations of Lemmas D.2--D.7.  This theorem combines
them and proves the paper's deliberately loose `9 / T` failure budget; it does
not prove the six component concentration lemmas. -/
theorem measure_sourceGoodEventSet_compl_le_nine_div
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (family : DelayedSAPOGoodEventFailureFamily Omega)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (hbsc : mu family.bscConfidence <=
      ENNReal.ofReal (quadraticFailureBudget horizon))
    (heap : mu family.eapConfidence <=
      ENNReal.ofReal (quadraticFailureBudget horizon))
    (hpull : mu family.pullCount <=
      ENNReal.ofReal (quadraticFailureBudget horizon))
    (heliminated : mu family.eliminatedDelay <=
      ENNReal.ofReal (linearFailureBudget horizon))
    (hloss : mu family.lossDifference <=
      ENNReal.ofReal (linearFailureBudget horizon))
    (hdelay : mu family.stochasticDelay <=
      ENNReal.ofReal (linearFailureBudget horizon)) :
    mu family.sourceGoodEventSetᶜ <=
      ENNReal.ofReal (9 / (horizon : Real)) := by
  have hquadratic := quadraticFailureBudget_le_linearFailureBudget
    horizon hhorizon
  have hcomponent : forall component,
      mu (family.componentFailure component) <=
        ENNReal.ofReal (linearFailureBudget horizon) := by
    intro component
    cases component with
    | bscConfidence =>
        exact hbsc.trans (ENNReal.ofReal_le_ofReal hquadratic)
    | eapConfidence =>
        exact heap.trans (ENNReal.ofReal_le_ofReal hquadratic)
    | pullCount =>
        exact hpull.trans (ENNReal.ofReal_le_ofReal hquadratic)
    | eliminatedDelay => exact heliminated
    | lossDifference => exact hloss
    | stochasticDelay => exact hdelay
  have hsum := family.measure_sourceGoodEventSet_compl_le_sum mu
  have hlinear_nonneg : 0 <= linearFailureBudget horizon := by
    dsimp [linearFailureBudget]
    positivity
  have hcomponent_card : Fintype.card DelayedSAPOGoodEventComponent = 6 := by
    decide
  have hsumBudget :
      (Finset.univ : Finset DelayedSAPOGoodEventComponent).sum
          (fun component => mu (family.componentFailure component)) <=
        ENNReal.ofReal (6 * linearFailureBudget horizon) := by
    calc
      _ <= (Finset.univ : Finset DelayedSAPOGoodEventComponent).sum
          (fun _component => ENNReal.ofReal (linearFailureBudget horizon)) := by
        exact Finset.sum_le_sum fun component _ => hcomponent component
      _ = 6 * ENNReal.ofReal (linearFailureBudget horizon) := by
        rw [Finset.sum_const, Finset.card_univ, hcomponent_card]
        simp [nsmul_eq_mul]
      _ = ENNReal.ofReal (6 * linearFailureBudget horizon) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 6)]
        norm_num
  have hreal :
      6 * linearFailureBudget horizon <= 9 / (horizon : Real) := by
    dsimp [linearFailureBudget]
    have hinv : 0 <= 1 / (horizon : Real) := by positivity
    calc
      6 * (1 / (horizon : Real)) <= 9 * (1 / (horizon : Real)) := by
        gcongr
        norm_num
      _ = 9 / (horizon : Real) := by ring
  exact hsum.trans (hsumBudget.trans (ENNReal.ofReal_le_ofReal hreal))

/-- The full source good event implies the already compiled elimination slice
when the projection relation is recorded explicitly. -/
theorem measure_eliminationGoodEventSet_compl_le_nine_div
    {Omega : Type*} [MeasurableSpace Omega]
    {K : Nat} [Nonempty (Fin K)]
    (mu : Measure Omega)
    (family : DelayedSAPOGoodEventFailureFamily Omega)
    (snapshot : Omega -> DelayedSAPOSourceConfidenceSnapshot K)
    (mean : Fin K -> Real)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (hprojection : family.sourceGoodEventSet ⊆
      DelayedSAPOSourceConfidenceSnapshot.eliminationGoodEventSet snapshot mean)
    (hbsc : mu family.bscConfidence <=
      ENNReal.ofReal (quadraticFailureBudget horizon))
    (heap : mu family.eapConfidence <=
      ENNReal.ofReal (quadraticFailureBudget horizon))
    (hpull : mu family.pullCount <=
      ENNReal.ofReal (quadraticFailureBudget horizon))
    (heliminated : mu family.eliminatedDelay <=
      ENNReal.ofReal (linearFailureBudget horizon))
    (hloss : mu family.lossDifference <=
      ENNReal.ofReal (linearFailureBudget horizon))
    (hdelay : mu family.stochasticDelay <=
      ENNReal.ofReal (linearFailureBudget horizon)) :
    mu (DelayedSAPOSourceConfidenceSnapshot.eliminationGoodEventSet
      snapshot mean)ᶜ <= ENNReal.ofReal (9 / (horizon : Real)) := by
  have hmono :
      mu (DelayedSAPOSourceConfidenceSnapshot.eliminationGoodEventSet
          snapshot mean)ᶜ <= mu family.sourceGoodEventSetᶜ := by
    exact measure_mono (Set.compl_subset_compl.mpr hprojection)
  exact hmono.trans (family.measure_sourceGoodEventSet_compl_le_nine_div
    mu horizon hhorizon hbsc heap hpull heliminated hloss hdelay)

/-- Corollary D.8 composed with the compiled one-snapshot D.9 projection:
component failure budgets control optimal-arm elimination.  Recursive
persistence and both regret endpoints remain separate obligations. -/
theorem measure_optimalSurvivalEventSet_compl_le_nine_div
    {Omega : Type*} [MeasurableSpace Omega]
    {K : Nat} [Nonempty (Fin K)]
    (mu : Measure Omega)
    (family : DelayedSAPOGoodEventFailureFamily Omega)
    (snapshot : Omega -> DelayedSAPOSourceConfidenceSnapshot K)
    (mean : Fin K -> Real) (optimal : Fin K)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (hoptimal : forall i, mean optimal <= mean i)
    (hactive : forall omega, optimal ∈ (snapshot omega).active)
    (hprojection : family.sourceGoodEventSet ⊆
      DelayedSAPOSourceConfidenceSnapshot.eliminationGoodEventSet snapshot mean)
    (hbsc : mu family.bscConfidence <=
      ENNReal.ofReal (quadraticFailureBudget horizon))
    (heap : mu family.eapConfidence <=
      ENNReal.ofReal (quadraticFailureBudget horizon))
    (hpull : mu family.pullCount <=
      ENNReal.ofReal (quadraticFailureBudget horizon))
    (heliminated : mu family.eliminatedDelay <=
      ENNReal.ofReal (linearFailureBudget horizon))
    (hloss : mu family.lossDifference <=
      ENNReal.ofReal (linearFailureBudget horizon))
    (hdelay : mu family.stochasticDelay <=
      ENNReal.ofReal (linearFailureBudget horizon)) :
    mu (DelayedSAPOSourceConfidenceSnapshot.optimalSurvivalEventSet
      snapshot optimal)ᶜ <= ENNReal.ofReal (9 / (horizon : Real)) := by
  exact (DelayedSAPOSourceConfidenceSnapshot.measure_optimalSurvivalEventSet_compl_le
    mu snapshot mean optimal hoptimal hactive).trans
      (family.measure_eliminationGoodEventSet_compl_le_nine_div
        mu snapshot mean horizon hhorizon hprojection hbsc heap hpull
        heliminated hloss hdelay)

end DelayedSAPOGoodEventFailureFamily

end DelayedFeedback

end BanditRLProof
