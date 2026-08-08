import BanditRLProof.TsallisFTRLRegret
import BanditRLProof.TsallisImportanceWeightedMoment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Half-Tsallis FTRL one-step stability

This module proves the deterministic one-step stability estimate used by the
`alpha = 1 / 2` Tsallis-INF route.  It consumes explicit interior stationarity
certificates for the current and importance-weighted updated distributions.
The certificates expose exactly the KKT equation for the local objective
`eta * <p, score> + negEntropyRegularizer arms (1 / 2) p`.

The final theorem averages the pathwise stability term over the current finite
simplex and bounds it by `2 * eta * sum_a sqrt (p a)`.  It does not derive the
stationarity certificates from minimizer certificates, prove minimizer
interiority/existence, or perform a conditional-expectation transport.

This is a valid but looser route for the stability term in the local FTRL
decomposition, not a literal port of the conjugate-potential stability bound in
Tsallis-INF Lemmas 11/19.  Matching the paper's half-Tsallis regularizer scaling
uses `eta_local = eta_paper / 2` up to simplex-constant terms; the bound here is
then `eta_paper * sum_a sqrt (p a)`, twice the comparable Lemma 11 coefficient.
-/

namespace BanditRLProof
namespace Tsallis

universe u

/--
Interior first-order stationarity for the half-Tsallis regularizer.

For `alpha = 1 / 2`, the coordinate derivative of the local negative Tsallis
entropy is `-p_a^(-1/2)`.  The common multiplier records the simplex equality
constraint; positivity and normalization are kept as separate theorem inputs.
-/
def HalfTsallisInteriorStationary {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (score p : Action -> Real) (multiplier : Real) : Prop :=
  forall action, action ∈ arms ->
    eta * score action - (p action) ^ (-(1 / 2 : Real)) = multiplier

/-- Subtracting two half-Tsallis stationarity equations isolates the update. -/
theorem halfTsallisInteriorStationary_rpow_sub_rpow_eq
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (score increment p q : Action -> Real)
    (multiplier nextMultiplier : Real)
    (hp : HalfTsallisInteriorStationary
      arms eta score p multiplier)
    (hq : HalfTsallisInteriorStationary
      arms eta (fun action => score action + increment action)
        q nextMultiplier)
    {action : Action} (haction : action ∈ arms) :
    (q action) ^ (-(1 / 2 : Real)) -
        (p action) ^ (-(1 / 2 : Real)) =
      eta * increment action - (nextMultiplier - multiplier) := by
  have hpAction := hp action haction
  have hqAction := hq action haction
  dsimp only at hqAction
  linarith

/--
Scalar half-Tsallis curvature inequality on the positive cone.

This is the one-dimensional inequality that converts a negative-half-power
gradient displacement into a displacement of probability mass.
-/
theorem sub_le_two_mul_rpow_three_halves_mul_neg_half_rpow_sub
    {p q : Real} (hp : 0 < p) (hq : 0 < q) (hqp : q <= p) :
    p - q <=
      2 * p ^ (3 / 2 : Real) *
        (q ^ (-(1 / 2 : Real)) - p ^ (-(1 / 2 : Real))) := by
  have hsqrtPPos : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsqrtQPos : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsqrtLe : Real.sqrt q <= Real.sqrt p := Real.sqrt_le_sqrt hqp
  have hsqrtPSq : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp.le
  have hsqrtQSq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
  have hdiff :
      q ^ (-(1 / 2 : Real)) - p ^ (-(1 / 2 : Real)) =
        (Real.sqrt p - Real.sqrt q) /
          (Real.sqrt p * Real.sqrt q) := by
    rw [Real.rpow_neg hq.le, Real.rpow_neg hp.le]
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    field_simp [ne_of_gt hsqrtPPos, ne_of_gt hsqrtQPos]
  have hdiffNonneg :
      0 <= q ^ (-(1 / 2 : Real)) - p ^ (-(1 / 2 : Real)) := by
    rw [hdiff]
    exact div_nonneg (sub_nonneg.2 hsqrtLe)
      (mul_nonneg hsqrtPPos.le hsqrtQPos.le)
  have hfactorLe :
      Real.sqrt p * Real.sqrt q * (Real.sqrt p + Real.sqrt q) <=
        2 * p ^ (3 / 2 : Real) := by
    have hsumLe :
        Real.sqrt p + Real.sqrt q <=
          Real.sqrt p + Real.sqrt p := by
      linarith
    have hinner :
        Real.sqrt q * (Real.sqrt p + Real.sqrt q) <=
          Real.sqrt p * (Real.sqrt p + Real.sqrt p) :=
      mul_le_mul hsqrtLe hsumLe
        (add_nonneg hsqrtPPos.le hsqrtQPos.le) hsqrtPPos.le
    have hscaled := mul_le_mul_of_nonneg_left hinner hsqrtPPos.le
    have hrpow :
        p ^ (3 / 2 : Real) = p * Real.sqrt p := by
      rw [show (3 / 2 : Real) = 1 + 1 / 2 by norm_num,
        Real.rpow_add hp, Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [hrpow]
    nlinarith
  have hfactor :
      p - q =
        (q ^ (-(1 / 2 : Real)) - p ^ (-(1 / 2 : Real))) *
          (Real.sqrt p * Real.sqrt q *
            (Real.sqrt p + Real.sqrt q)) := by
    rw [hdiff]
    field_simp [ne_of_gt hsqrtPPos, ne_of_gt hsqrtQPos]
    nlinarith
  rw [hfactor]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left hfactorLe hdiffNonneg

/--
Pathwise half-Tsallis FTRL stability for one importance-weighted observation.

The current and updated distributions are normalized and strictly positive on
`arms`.  Their stationarity certificates force the multiplier displacement to
lie between zero and the selected coordinate update; the scalar curvature
lemma then controls the one-step linear-loss difference.
-/
theorem linearLoss_sub_next_importanceWeightedLoss_le
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (score prob next loss : Action -> Real) (chosen : Action)
    (multiplier nextMultiplier : Real)
    (hchosen : chosen ∈ arms) (heta : 0 < eta)
    (hprobSimplex : FTRL.finiteSimplex arms prob)
    (hnextSimplex : FTRL.finiteSimplex arms next)
    (hprobPos : forall action, action ∈ arms -> 0 < prob action)
    (hnextPos : forall action, action ∈ arms -> 0 < next action)
    (hlossNonneg : forall action, action ∈ arms -> 0 <= loss action)
    (hprobStationary : HalfTsallisInteriorStationary
      arms eta score prob multiplier)
    (hnextStationary : HalfTsallisInteriorStationary
      arms eta
        (fun action => score action +
          Exp3.importanceWeightedLoss prob loss chosen action)
        next nextMultiplier) :
    FTRL.linearLoss arms prob
          (Exp3.importanceWeightedLoss prob loss chosen) -
        FTRL.linearLoss arms next
          (Exp3.importanceWeightedLoss prob loss chosen) <=
      2 * eta *
        powerWeightedSquaredImportanceWeightedLoss
          arms (1 / 2 : Real) prob loss chosen := by
  let shift := nextMultiplier - multiplier
  let observed := loss chosen / prob chosen
  have hnegHalf : (-(1 / 2 : Real)) < 0 := by norm_num
  have hprobChosen : 0 < prob chosen := hprobPos chosen hchosen
  have hnextChosen : 0 < next chosen := hnextPos chosen hchosen
  have hlossChosen : 0 <= loss chosen := hlossNonneg chosen hchosen
  have hobservedNonneg : 0 <= observed :=
    div_nonneg hlossChosen hprobChosen.le
  have hdiff : forall action, action ∈ arms ->
      (next action) ^ (-(1 / 2 : Real)) -
          (prob action) ^ (-(1 / 2 : Real)) =
        eta * Exp3.importanceWeightedLoss prob loss chosen action - shift := by
    intro action haction
    exact halfTsallisInteriorStationary_rpow_sub_rpow_eq
      arms eta score
      (Exp3.importanceWeightedLoss prob loss chosen)
      prob next multiplier nextMultiplier
      hprobStationary hnextStationary haction
  have hshiftNonneg : 0 <= shift := by
    by_contra hnot
    have hshiftNeg : shift < 0 := lt_of_not_ge hnot
    have hsumLt : arms.sum next < arms.sum prob :=
      Finset.sum_lt_sum_of_nonempty ⟨chosen, hchosen⟩ (by
        intro action haction
        have hiwNonneg :
            0 <= Exp3.importanceWeightedLoss prob loss chosen action :=
          Exp3.importanceWeightedLoss_nonneg
            (hprobSimplex.1 action haction)
            (hlossNonneg action haction)
        have hpowerLt :
            (prob action) ^ (-(1 / 2 : Real)) <
              (next action) ^ (-(1 / 2 : Real)) := by
          have := hdiff action haction
          nlinarith [mul_nonneg heta.le hiwNonneg]
        exact (Real.rpow_lt_rpow_iff_of_neg
          (hprobPos action haction) (hnextPos action haction)
          hnegHalf).1 hpowerLt)
    rw [hprobSimplex.2, hnextSimplex.2] at hsumLt
    exact (lt_irrefl 1 hsumLt)
  have hshiftLe : shift <= eta * observed := by
    by_contra hnot
    have hselectedLtShift : eta * observed < shift := lt_of_not_ge hnot
    have hsumLt : arms.sum prob < arms.sum next :=
      Finset.sum_lt_sum_of_nonempty ⟨chosen, hchosen⟩ (by
        intro action haction
        have hiwLe :
            Exp3.importanceWeightedLoss prob loss chosen action <= observed := by
          by_cases heq : chosen = action
          · subst action
            simp [Exp3.importanceWeightedLoss, observed]
          · simp [Exp3.importanceWeightedLoss, heq, hobservedNonneg]
        have hetaIWLt :
            eta * Exp3.importanceWeightedLoss prob loss chosen action < shift :=
          (mul_le_mul_of_nonneg_left hiwLe heta.le).trans_lt hselectedLtShift
        have hpowerLt :
            (next action) ^ (-(1 / 2 : Real)) <
              (prob action) ^ (-(1 / 2 : Real)) := by
          have := hdiff action haction
          linarith
        exact (Real.rpow_lt_rpow_iff_of_neg
          (hnextPos action haction) (hprobPos action haction)
          hnegHalf).1 hpowerLt)
    rw [hprobSimplex.2, hnextSimplex.2] at hsumLt
    exact (lt_irrefl 1 hsumLt)
  have hiwChosen :
      Exp3.importanceWeightedLoss prob loss chosen chosen = observed := by
    simp [Exp3.importanceWeightedLoss, observed]
  have hchosenDiff :
      (next chosen) ^ (-(1 / 2 : Real)) -
          (prob chosen) ^ (-(1 / 2 : Real)) =
        eta * observed - shift := by
    simpa [hiwChosen] using hdiff chosen hchosen
  have hchosenDiffNonneg :
      0 <= (next chosen) ^ (-(1 / 2 : Real)) -
        (prob chosen) ^ (-(1 / 2 : Real)) := by
    rw [hchosenDiff]
    linarith
  have hnextLe : next chosen <= prob chosen := by
    apply (Real.rpow_le_rpow_iff_of_neg
      hprobChosen hnextChosen hnegHalf).1
    linarith
  have hcurvature :=
    sub_le_two_mul_rpow_three_halves_mul_neg_half_rpow_sub
      hprobChosen hnextChosen hnextLe
  have hdiffLe :
      (next chosen) ^ (-(1 / 2 : Real)) -
          (prob chosen) ^ (-(1 / 2 : Real)) <= eta * observed := by
    rw [hchosenDiff]
    linarith
  have hlinear :
      FTRL.linearLoss arms prob
            (Exp3.importanceWeightedLoss prob loss chosen) -
          FTRL.linearLoss arms next
            (Exp3.importanceWeightedLoss prob loss chosen) =
        (prob chosen - next chosen) * observed := by
    unfold FTRL.linearLoss
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single chosen]
    · simp [Exp3.importanceWeightedLoss, observed]
      ring
    · intro action haction hne
      simp [Exp3.importanceWeightedLoss, Ne.symm hne]
    · exact fun hnotmem => (hnotmem hchosen).elim
  have hscaledCurvature :
      (prob chosen - next chosen) * observed <=
        (2 * (prob chosen) ^ (3 / 2 : Real) *
          ((next chosen) ^ (-(1 / 2 : Real)) -
            (prob chosen) ^ (-(1 / 2 : Real)))) * observed :=
    mul_le_mul_of_nonneg_right hcurvature hobservedNonneg
  have hscaledDiff :
      (2 * (prob chosen) ^ (3 / 2 : Real) *
          ((next chosen) ^ (-(1 / 2 : Real)) -
            (prob chosen) ^ (-(1 / 2 : Real)))) * observed <=
        (2 * (prob chosen) ^ (3 / 2 : Real) *
          (eta * observed)) * observed := by
    have hcoeffNonneg :
        0 <= 2 * (prob chosen) ^ (3 / 2 : Real) := by positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdiffLe hcoeffNonneg)
      hobservedNonneg
  have hpow :
      (prob chosen) ^ (3 / 2 : Real) =
        (prob chosen) ^ (2 : Real) *
          (prob chosen) ^ (-(1 / 2 : Real)) := by
    rw [← Real.rpow_add hprobChosen]
    congr 1
    norm_num
  rw [hlinear]
  calc
    (prob chosen - next chosen) * observed <=
        (2 * (prob chosen) ^ (3 / 2 : Real) *
          ((next chosen) ^ (-(1 / 2 : Real)) -
            (prob chosen) ^ (-(1 / 2 : Real)))) * observed :=
      hscaledCurvature
    _ <= (2 * (prob chosen) ^ (3 / 2 : Real) *
          (eta * observed)) * observed := hscaledDiff
    _ = 2 * eta * ((loss chosen) ^ 2 *
          (prob chosen) ^ (-(1 / 2 : Real))) := by
      rw [hpow, Real.rpow_two]
      dsimp only [observed]
      field_simp [ne_of_gt hprobChosen]
    _ = 2 * eta *
          powerWeightedSquaredImportanceWeightedLoss
            arms (1 / 2 : Real) prob loss chosen := by
      rw [powerWeightedSquaredImportanceWeightedLoss_eq_selected
        arms (1 / 2 : Real) prob loss chosen hchosen hprobChosen]

/--
Sampling-law finite-sum half-Tsallis stability bound.

For every possible sampled action, `next chosen` carries its own updated
stationarity certificate.  Averaging the pathwise FTRL stability terms with
the current simplex masses is bounded by `2 * eta` times the half-power sum.
-/
theorem sum_prob_mul_linearLoss_sub_next_importanceWeightedLoss_le_powerSum_half
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (eta : Real)
    (score prob loss : Action -> Real)
    (next : Action -> Action -> Real)
    (multiplier : Real) (nextMultiplier : Action -> Real)
    (heta : 0 < eta)
    (hprobSimplex : FTRL.finiteSimplex arms prob)
    (hprobPos : forall action, action ∈ arms -> 0 < prob action)
    (hnextSimplex : forall chosen, chosen ∈ arms ->
      FTRL.finiteSimplex arms (next chosen))
    (hnextPos : forall chosen, chosen ∈ arms ->
      forall action, action ∈ arms -> 0 < next chosen action)
    (hloss : forall action, action ∈ arms ->
      0 <= loss action ∧ loss action <= 1)
    (hprobStationary : HalfTsallisInteriorStationary
      arms eta score prob multiplier)
    (hnextStationary : forall chosen, chosen ∈ arms ->
      HalfTsallisInteriorStationary
        arms eta
          (fun action => score action +
            Exp3.importanceWeightedLoss prob loss chosen action)
          (next chosen) (nextMultiplier chosen)) :
    arms.sum (fun chosen =>
        prob chosen *
          (FTRL.linearLoss arms prob
              (Exp3.importanceWeightedLoss prob loss chosen) -
            FTRL.linearLoss arms (next chosen)
              (Exp3.importanceWeightedLoss prob loss chosen))) <=
      2 * eta * powerSum arms (1 / 2 : Real) prob := by
  have hpathwise : forall chosen, chosen ∈ arms ->
      FTRL.linearLoss arms prob
            (Exp3.importanceWeightedLoss prob loss chosen) -
          FTRL.linearLoss arms (next chosen)
            (Exp3.importanceWeightedLoss prob loss chosen) <=
        2 * eta *
          powerWeightedSquaredImportanceWeightedLoss
            arms (1 / 2 : Real) prob loss chosen := by
    intro chosen hchosen
    exact linearLoss_sub_next_importanceWeightedLoss_le
      arms eta score prob (next chosen) loss chosen
      multiplier (nextMultiplier chosen) hchosen heta
      hprobSimplex (hnextSimplex chosen hchosen) hprobPos
      (hnextPos chosen hchosen) (fun action haction =>
        (hloss action haction).1)
      hprobStationary (hnextStationary chosen hchosen)
  have hmoment :=
    sum_prob_mul_powerWeightedSquaredImportanceWeightedLoss_le_powerSum
      arms (1 / 2 : Real) prob loss hprobPos hloss
  calc
    arms.sum (fun chosen =>
        prob chosen *
          (FTRL.linearLoss arms prob
              (Exp3.importanceWeightedLoss prob loss chosen) -
            FTRL.linearLoss arms (next chosen)
              (Exp3.importanceWeightedLoss prob loss chosen))) <=
        arms.sum (fun chosen =>
          prob chosen *
            (2 * eta *
              powerWeightedSquaredImportanceWeightedLoss
                arms (1 / 2 : Real) prob loss chosen)) := by
      apply Finset.sum_le_sum
      intro chosen hchosen
      exact mul_le_mul_of_nonneg_left (hpathwise chosen hchosen)
        (hprobSimplex.1 chosen hchosen)
    _ = 2 * eta *
        arms.sum (fun chosen =>
          prob chosen *
            powerWeightedSquaredImportanceWeightedLoss
              arms (1 / 2 : Real) prob loss chosen) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chosen _hchosen
      ring
    _ <= 2 * eta * powerSum arms (1 - (1 / 2 : Real)) prob := by
      exact mul_le_mul_of_nonneg_left hmoment (mul_nonneg (by norm_num) heta.le)
    _ = 2 * eta * powerSum arms (1 / 2 : Real) prob := by norm_num

end Tsallis
end BanditRLProof
