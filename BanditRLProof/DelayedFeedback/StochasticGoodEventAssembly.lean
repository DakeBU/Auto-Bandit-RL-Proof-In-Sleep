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

/-- The source `1 / T` budget used for Lemmas D.5--D.7. -/
noncomputable def linearFailureBudget (horizon : Nat) : Real :=
  1 / (horizon : Real)

/-- The source `2 / T` budget used for Lemmas D.2--D.4. -/
noncomputable def doubleLinearFailureBudget (horizon : Nat) : Real :=
  2 / (horizon : Real)

/-- The source-exact failure share assigned to each clause in Corollary D.8:
D.2--D.4 contribute `2 / T` each and D.5--D.7 contribute `1 / T` each. -/
noncomputable def sourceComponentFailureBudget (horizon : Nat) :
    DelayedSAPOGoodEventComponent -> Real
  | .bscConfidence => doubleLinearFailureBudget horizon
  | .eapConfidence => doubleLinearFailureBudget horizon
  | .pullCount => doubleLinearFailureBudget horizon
  | .eliminatedDelay => linearFailureBudget horizon
  | .lossDifference => linearFailureBudget horizon
  | .stochasticDelay => linearFailureBudget horizon

/-- The six source-exact shares in Corollary D.8 sum to `9 / T`. -/
theorem sum_sourceComponentFailureBudget_eq_nine_div
    (horizon : Nat) :
    (Finset.univ : Finset DelayedSAPOGoodEventComponent).sum
        (sourceComponentFailureBudget horizon) =
      9 / (horizon : Real) := by
  have huniv :
      (Finset.univ : Finset DelayedSAPOGoodEventComponent) =
        {.bscConfidence, .eapConfidence, .pullCount, .eliminatedDelay,
          .lossDifference, .stochasticDelay} := by
    decide
  rw [huniv]
  simp [sourceComponentFailureBudget, doubleLinearFailureBudget,
    linearFailureBudget]
  ring

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
      ENNReal.ofReal (doubleLinearFailureBudget horizon))
    (heap : mu family.eapConfidence <=
      ENNReal.ofReal (doubleLinearFailureBudget horizon))
    (hpull : mu family.pullCount <=
      ENNReal.ofReal (doubleLinearFailureBudget horizon))
    (heliminated : mu family.eliminatedDelay <=
      ENNReal.ofReal (linearFailureBudget horizon))
    (hloss : mu family.lossDifference <=
      ENNReal.ofReal (linearFailureBudget horizon))
    (hdelay : mu family.stochasticDelay <=
      ENNReal.ofReal (linearFailureBudget horizon)) :
    mu family.sourceGoodEventSetᶜ <=
      ENNReal.ofReal (9 / (horizon : Real)) := by
  have hcomponent : forall component,
      mu (family.componentFailure component) <=
        ENNReal.ofReal (sourceComponentFailureBudget horizon component) := by
    intro component
    cases component with
    | bscConfidence => exact hbsc
    | eapConfidence => exact heap
    | pullCount => exact hpull
    | eliminatedDelay => exact heliminated
    | lossDifference => exact hloss
    | stochasticDelay => exact hdelay
  have hsum := family.measure_sourceGoodEventSet_compl_le_sum mu
  have hsumBudget :
      (Finset.univ : Finset DelayedSAPOGoodEventComponent).sum
          (fun component => mu (family.componentFailure component)) <=
        ENNReal.ofReal (9 / (horizon : Real)) := by
    calc
      _ <= (Finset.univ : Finset DelayedSAPOGoodEventComponent).sum
          (fun component => ENNReal.ofReal
            (sourceComponentFailureBudget horizon component)) := by
        exact Finset.sum_le_sum fun component _ => hcomponent component
      _ = ENNReal.ofReal
          ((Finset.univ : Finset DelayedSAPOGoodEventComponent).sum
            (sourceComponentFailureBudget horizon)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro component _hcomponent
        cases component <;>
          simp [sourceComponentFailureBudget, doubleLinearFailureBudget,
            linearFailureBudget] <;> positivity
      _ = ENNReal.ofReal (9 / (horizon : Real)) := by
        rw [sum_sourceComponentFailureBudget_eq_nine_div]
  exact hsum.trans hsumBudget

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
      ENNReal.ofReal (doubleLinearFailureBudget horizon))
    (heap : mu family.eapConfidence <=
      ENNReal.ofReal (doubleLinearFailureBudget horizon))
    (hpull : mu family.pullCount <=
      ENNReal.ofReal (doubleLinearFailureBudget horizon))
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
      ENNReal.ofReal (doubleLinearFailureBudget horizon))
    (heap : mu family.eapConfidence <=
      ENNReal.ofReal (doubleLinearFailureBudget horizon))
    (hpull : mu family.pullCount <=
      ENNReal.ofReal (doubleLinearFailureBudget horizon))
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
