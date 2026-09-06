import BanditRLProof.Exp3Potential
import BanditRLProof.TsallisConjugatePotentialStability
import BanditRLProof.TsallisFTRLRegret
import BanditRLProof.TsallisSelfBounding
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Time-varying half-Tsallis penalty

This module formalizes the deterministic learning-rate-change term used by the
Tsallis-INF penalty route.  It telescopes paper-normalized half-Tsallis
potential values across a positive, nonincreasing schedule and retains the
negative terminal comparator contribution.

The result consumes finite-simplex minimizer certificates only.  It does not
construct a stochastic trajectory, prove conditional stability, choose a
specific schedule, or conclude a bandit regret theorem.
-/

namespace BanditRLProof
namespace Tsallis

universe u

/-- The paper-normalized regularizer mass carried by the local potential. -/
noncomputable def halfTsallisPotentialMass {Action : Type u}
    (arms : Finset Action) (p : Action -> Real) : Real :=
  1 - negEntropyRegularizer arms (1 / 2 : Real) p

/-- The regularizer mass is `2 * sum sqrt(p_a) - 1`. -/
theorem halfTsallisPotentialMass_eq_two_mul_powerSum_sub_one
    {Action : Type u}
    (arms : Finset Action) (p : Action -> Real) :
    halfTsallisPotentialMass arms p =
      2 * powerSum arms (1 / 2 : Real) p - 1 := by
  simp [halfTsallisPotentialMass, negEntropyRegularizer, entropy]
  ring

/-- A supported point mass has paper-normalized potential mass one. -/
theorem halfTsallisPotentialMass_pointMass
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {best : Action} (hbest : best ∈ arms) :
    halfTsallisPotentialMass arms (pointMass best) = 1 := by
  rw [halfTsallisPotentialMass_eq_two_mul_powerSum_sub_one,
    powerSum_pointMass_half arms hbest]
  ring

/-- The potential is linear loss with the regularizer mass divided by `eta`. -/
theorem halfTsallisPotentialValue_eq_neg_linearLoss_add_mass_div
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (score p : Action -> Real) (heta : eta ≠ 0) :
    halfTsallisPotentialValue arms eta score p =
      -FTRL.linearLoss arms p score + halfTsallisPotentialMass arms p / eta := by
  unfold halfTsallisPotentialValue halfTsallisPotentialMass
  rw [FTRL.regularizedObjective]
  field_simp [heta]
  ring

/-- A regularized-objective minimizer maximizes the corresponding potential. -/
theorem halfTsallisPotentialValue_le_of_isRegularizedMinimizer
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (score p q : Action -> Real) (heta : 0 < eta)
    (hp : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) score p)
    (hq : FTRL.finiteSimplex arms q) :
    halfTsallisPotentialValue arms eta score q <=
      halfTsallisPotentialValue arms eta score p := by
  have hobjective := hp.2 q hq
  have hscaled :
      FTRL.regularizedObjective arms eta
          (negEntropyRegularizer arms (1 / 2 : Real)) score p / eta <=
        FTRL.regularizedObjective arms eta
          (negEntropyRegularizer arms (1 / 2 : Real)) score q / eta :=
    (div_le_div_iff_of_pos_right heta).2 hobjective
  unfold halfTsallisPotentialValue
  simpa [neg_div, add_comm] using
    add_le_add_right (neg_le_neg hscaled) (1 / eta)

/-- Changing the learning rate at a fixed score costs the reciprocal-rate
increment times the mass of the new minimizer. -/
theorem halfTsallisPotentialValue_new_sub_old_le_rateChange_mul_mass
    {Action : Type u}
    (arms : Finset Action) (etaOld etaNew : Real)
    (score pOld pNew : Action -> Real)
    (hetaOld : 0 < etaOld) (hetaNew : 0 < etaNew)
    (hpOld : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms etaOld (negEntropyRegularizer arms (1 / 2 : Real)) score pOld)
    (hpNew : FTRL.finiteSimplex arms pNew) :
    halfTsallisPotentialValue arms etaNew score pNew -
        halfTsallisPotentialValue arms etaOld score pOld <=
      (1 / etaNew - 1 / etaOld) * halfTsallisPotentialMass arms pNew := by
  have hpotential :=
    halfTsallisPotentialValue_le_of_isRegularizedMinimizer
      arms etaOld score pOld pNew hetaOld hpOld hpNew
  calc
    halfTsallisPotentialValue arms etaNew score pNew -
        halfTsallisPotentialValue arms etaOld score pOld <=
      halfTsallisPotentialValue arms etaNew score pNew -
        halfTsallisPotentialValue arms etaOld score pNew :=
      sub_le_sub_left hpotential _
    _ = (1 / etaNew - 1 / etaOld) *
        halfTsallisPotentialMass arms pNew := by
      rw [halfTsallisPotentialValue_eq_neg_linearLoss_add_mass_div
          arms etaNew score pNew (ne_of_gt hetaNew),
        halfTsallisPotentialValue_eq_neg_linearLoss_add_mass_div
          arms etaOld score pNew (ne_of_gt hetaOld)]
      ring

/-- A zero-score minimizer maximizes the half-Tsallis regularizer mass. -/
theorem halfTsallisPotentialMass_le_of_zero_isRegularizedMinimizer
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (p q : Action -> Real) (heta : 0 < eta)
    (hp : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms eta (negEntropyRegularizer arms (1 / 2 : Real)) (fun _ => 0) p)
    (hq : FTRL.finiteSimplex arms q) :
    halfTsallisPotentialMass arms q <= halfTsallisPotentialMass arms p := by
  have hpotential :=
    halfTsallisPotentialValue_le_of_isRegularizedMinimizer
      arms eta (fun _ => 0) p q heta hp hq
  rw [halfTsallisPotentialValue_eq_neg_linearLoss_add_mass_div
        arms eta (fun _ => 0) q (ne_of_gt heta),
      halfTsallisPotentialValue_eq_neg_linearLoss_add_mass_div
        arms eta (fun _ => 0) p (ne_of_gt heta)] at hpotential
  simp [FTRL.linearLoss] at hpotential
  exact (div_le_div_iff_of_pos_right heta).1 hpotential

/-- Algebraic telescope with different left and right endpoint processes. -/
theorem sum_range_succ_sub_eq_first_sub_last_add_cross
    (A B : Nat -> Real) (n : Nat) :
    (Finset.range (n + 1)).sum (fun t => A t - B t) =
      A 0 - B n +
        (Finset.range n).sum (fun t => A (t + 1) - B t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- Canonical scheduled minimizer before round `t`. -/
noncomputable def halfTsallisScheduledMinimizer
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real) (loss : Nat -> Action -> Real) (t : Nat) :
    Action -> Real :=
  halfTsallisMinimizer arms harms (eta t) (FTRL.cumulativeLoss loss t)

/-- Canonical same-rate auxiliary minimizer after appending round `t`. -/
noncomputable def halfTsallisScheduledSameRateNext
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real) (loss : Nat -> Action -> Real) (t : Nat) :
    Action -> Real :=
  halfTsallisMinimizer arms harms (eta t) (FTRL.cumulativeLoss loss (t + 1))

/-- Deterministic time-varying potential penalty with its terminal comparator
contribution left explicit. -/
theorem sum_halfTsallisScheduledPotentialPenalty_le
    {Action : Type u}
    (arms : Finset Action) (eta : Nat -> Real)
    (loss : Nat -> Action -> Real)
    (current sameRateNext : Nat -> Action -> Real)
    (q : Action -> Real) (n : Nat)
    (heta : forall t, t <= n -> 0 < eta t)
    (hcurrent : forall t, t <= n ->
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms (eta t) (negEntropyRegularizer arms (1 / 2 : Real))
        (FTRL.cumulativeLoss loss t) (current t))
    (hnext : forall t, t <= n ->
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms (eta t) (negEntropyRegularizer arms (1 / 2 : Real))
        (FTRL.cumulativeLoss loss (t + 1)) (sameRateNext t))
    (hq : FTRL.finiteSimplex arms q) :
    (Finset.range (n + 1)).sum (fun t =>
        halfTsallisPotentialValue arms (eta t)
            (FTRL.cumulativeLoss loss t) (current t) -
          halfTsallisPotentialValue arms (eta t)
            (FTRL.cumulativeLoss loss (t + 1)) (sameRateNext t) -
          FTRL.linearLoss arms q (loss t)) <=
      halfTsallisPotentialMass arms (current 0) / eta 0 +
        (Finset.range n).sum (fun t =>
          (1 / eta (t + 1) - 1 / eta t) *
            halfTsallisPotentialMass arms (current (t + 1))) -
        halfTsallisPotentialMass arms q / eta n := by
  let A : Nat -> Real := fun t =>
    halfTsallisPotentialValue arms (eta t)
      (FTRL.cumulativeLoss loss t) (current t)
  let B : Nat -> Real := fun t =>
    halfTsallisPotentialValue arms (eta t)
      (FTRL.cumulativeLoss loss (t + 1)) (sameRateNext t)
  let C : Nat -> Real := fun t => FTRL.linearLoss arms q (loss t)
  have htelescope :
      (Finset.range (n + 1)).sum (fun t => (A t - B t) - C t) =
        A 0 - B n + (Finset.range n).sum (fun t => A (t + 1) - B t) -
          (Finset.range (n + 1)).sum C := by
    rw [Finset.sum_sub_distrib,
      sum_range_succ_sub_eq_first_sub_last_add_cross]
  have hcross :
      (Finset.range n).sum (fun t => A (t + 1) - B t) <=
        (Finset.range n).sum (fun t =>
          (1 / eta (t + 1) - 1 / eta t) *
            halfTsallisPotentialMass arms (current (t + 1))) := by
    apply Finset.sum_le_sum
    intro t ht
    have htn : t < n := Finset.mem_range.1 ht
    exact halfTsallisPotentialValue_new_sub_old_le_rateChange_mul_mass
      arms (eta t) (eta (t + 1)) (FTRL.cumulativeLoss loss (t + 1))
      (sameRateNext t) (current (t + 1))
      (heta t (Nat.le_of_lt htn))
      (heta (t + 1) (Nat.succ_le_of_lt htn))
      (hnext t (Nat.le_of_lt htn))
      (hcurrent (t + 1) (Nat.succ_le_of_lt htn)).1
  have hinitial :
      A 0 = halfTsallisPotentialMass arms (current 0) / eta 0 := by
    dsimp [A]
    rw [halfTsallisPotentialValue_eq_neg_linearLoss_add_mass_div
      arms (eta 0) (FTRL.cumulativeLoss loss 0) (current 0)
      (ne_of_gt (heta 0 (Nat.zero_le n)))]
    simp [FTRL.linearLoss]
  have hterminalPotential :=
    halfTsallisPotentialValue_le_of_isRegularizedMinimizer
      arms (eta n) (FTRL.cumulativeLoss loss (n + 1))
      (sameRateNext n) q (heta n le_rfl) (hnext n le_rfl) hq
  have hterminal :
      -B n - (Finset.range (n + 1)).sum C <=
        -halfTsallisPotentialMass arms q / eta n := by
    dsimp [B, C]
    rw [halfTsallisPotentialValue_eq_neg_linearLoss_add_mass_div
      arms (eta n) (FTRL.cumulativeLoss loss (n + 1)) q
      (ne_of_gt (heta n le_rfl))] at hterminalPotential
    rw [FTRL.linearLoss_cumulativeLoss] at hterminalPotential
    let S := (Finset.range (n + 1)).sum
      (fun t => FTRL.linearLoss arms q (loss t))
    let M := halfTsallisPotentialMass arms q / eta n
    let V := halfTsallisPotentialValue arms (eta n)
      (FTRL.cumulativeLoss loss (n + 1)) (sameRateNext n)
    change -S + M <= V at hterminalPotential
    have hbound : -V - S <= -M := by linarith
    simpa [V, S, M, neg_div] using hbound
  change (Finset.range (n + 1)).sum (fun t => (A t - B t) - C t) <= _
  rw [htelescope, hinitial]
  calc
    halfTsallisPotentialMass arms (current 0) / eta 0 - B n +
          (Finset.range n).sum (fun t => A (t + 1) - B t) -
        (Finset.range (n + 1)).sum C =
      halfTsallisPotentialMass arms (current 0) / eta 0 +
          (Finset.range n).sum (fun t => A (t + 1) - B t) +
        (-B n - (Finset.range (n + 1)).sum C) := by ring
    _ <= halfTsallisPotentialMass arms (current 0) / eta 0 +
          (Finset.range n).sum (fun t =>
            (1 / eta (t + 1) - 1 / eta t) *
              halfTsallisPotentialMass arms (current (t + 1))) +
        (-B n - (Finset.range (n + 1)).sum C) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (add_le_add_left hcross
            (halfTsallisPotentialMass arms (current 0) / eta 0))
          (-B n - (Finset.range (n + 1)).sum C)
    _ <= halfTsallisPotentialMass arms (current 0) / eta 0 +
          (Finset.range n).sum (fun t =>
            (1 / eta (t + 1) - 1 / eta t) *
              halfTsallisPotentialMass arms (current (t + 1))) +
        (-halfTsallisPotentialMass arms q / eta n) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hterminal
          (halfTsallisPotentialMass arms (current 0) / eta 0 +
            (Finset.range n).sum (fun t =>
              (1 / eta (t + 1) - 1 / eta t) *
                halfTsallisPotentialMass arms (current (t + 1))))
    _ = halfTsallisPotentialMass arms (current 0) / eta 0 +
          (Finset.range n).sum (fun t =>
            (1 / eta (t + 1) - 1 / eta t) *
              halfTsallisPotentialMass arms (current (t + 1))) -
        halfTsallisPotentialMass arms q / eta n := by ring

/-- Under a nonincreasing positive schedule, every rate-change mass is bounded
by the initial zero-score mass, so the reciprocal-rate increments telescope. -/
theorem sum_halfTsallisScheduledPotentialPenalty_le_initial_sub_comparator_div
    {Action : Type u}
    (arms : Finset Action) (eta : Nat -> Real)
    (loss : Nat -> Action -> Real)
    (current sameRateNext : Nat -> Action -> Real)
    (q : Action -> Real) (n : Nat)
    (heta : forall t, t <= n -> 0 < eta t)
    (hetaMono : forall t, t < n -> eta (t + 1) <= eta t)
    (hcurrent : forall t, t <= n ->
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms (eta t) (negEntropyRegularizer arms (1 / 2 : Real))
        (FTRL.cumulativeLoss loss t) (current t))
    (hnext : forall t, t <= n ->
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms (eta t) (negEntropyRegularizer arms (1 / 2 : Real))
        (FTRL.cumulativeLoss loss (t + 1)) (sameRateNext t))
    (hq : FTRL.finiteSimplex arms q) :
    (Finset.range (n + 1)).sum (fun t =>
        halfTsallisPotentialValue arms (eta t)
            (FTRL.cumulativeLoss loss t) (current t) -
          halfTsallisPotentialValue arms (eta t)
            (FTRL.cumulativeLoss loss (t + 1)) (sameRateNext t) -
          FTRL.linearLoss arms q (loss t)) <=
      (halfTsallisPotentialMass arms (current 0) -
        halfTsallisPotentialMass arms q) / eta n := by
  have hpenalty := sum_halfTsallisScheduledPotentialPenalty_le
    arms eta loss current sameRateNext q n heta hcurrent hnext hq
  have hmass : forall t, t < n ->
      halfTsallisPotentialMass arms (current (t + 1)) <=
        halfTsallisPotentialMass arms (current 0) := by
    intro t ht
    exact halfTsallisPotentialMass_le_of_zero_isRegularizedMinimizer
      arms (eta 0) (current 0) (current (t + 1))
      (heta 0 (Nat.zero_le n)) (by simpa using hcurrent 0 (Nat.zero_le n))
      (hcurrent (t + 1) (Nat.succ_le_of_lt ht)).1
  have hschedule :
      (Finset.range n).sum (fun t =>
          (1 / eta (t + 1) - 1 / eta t) *
            halfTsallisPotentialMass arms (current (t + 1))) <=
        (1 / eta n - 1 / eta 0) *
          halfTsallisPotentialMass arms (current 0) := by
    calc
      (Finset.range n).sum (fun t =>
          (1 / eta (t + 1) - 1 / eta t) *
            halfTsallisPotentialMass arms (current (t + 1))) <=
        (Finset.range n).sum (fun t =>
          (1 / eta (t + 1) - 1 / eta t) *
            halfTsallisPotentialMass arms (current 0)) := by
          apply Finset.sum_le_sum
          intro t ht
          have htn : t < n := Finset.mem_range.1 ht
          have hreciprocal : 1 / eta t <= 1 / eta (t + 1) :=
            one_div_le_one_div_of_le
              (heta (t + 1) (Nat.succ_le_of_lt htn)) (hetaMono t htn)
          exact mul_le_mul_of_nonneg_left (hmass t htn) (sub_nonneg.2 hreciprocal)
      _ = (1 / eta n - 1 / eta 0) *
          halfTsallisPotentialMass arms (current 0) := by
          rw [← Finset.sum_mul]
          exact congrArg
            (fun x : Real => x * halfTsallisPotentialMass arms (current 0))
            (Exp3Potential.sum_range_forward_difference
              (fun t => 1 / eta t) n)
  calc
    (Finset.range (n + 1)).sum (fun t =>
        halfTsallisPotentialValue arms (eta t)
            (FTRL.cumulativeLoss loss t) (current t) -
          halfTsallisPotentialValue arms (eta t)
            (FTRL.cumulativeLoss loss (t + 1)) (sameRateNext t) -
          FTRL.linearLoss arms q (loss t)) <=
      halfTsallisPotentialMass arms (current 0) / eta 0 +
        (Finset.range n).sum (fun t =>
          (1 / eta (t + 1) - 1 / eta t) *
            halfTsallisPotentialMass arms (current (t + 1))) -
        halfTsallisPotentialMass arms q / eta n := hpenalty
    _ <= halfTsallisPotentialMass arms (current 0) / eta 0 +
        (1 / eta n - 1 / eta 0) *
          halfTsallisPotentialMass arms (current 0) -
        halfTsallisPotentialMass arms q / eta n := by
      exact sub_le_sub_right
        (by
          simpa [add_comm] using add_le_add_right hschedule
            (halfTsallisPotentialMass arms (current 0) / eta 0)) _
    _ = (halfTsallisPotentialMass arms (current 0) -
        halfTsallisPotentialMass arms q) / eta n := by
      field_simp [ne_of_gt (heta 0 (Nat.zero_le n)), ne_of_gt (heta n le_rfl)]
      ring

/-- Canonical minimizer endpoint for the deterministic scheduled penalty. -/
theorem sum_halfTsallisCanonicalScheduledPotentialPenalty_le
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real) (loss : Nat -> Action -> Real)
    (q : Action -> Real) (n : Nat)
    (heta : forall t, t <= n -> 0 < eta t)
    (hetaMono : forall t, t < n -> eta (t + 1) <= eta t)
    (hq : FTRL.finiteSimplex arms q) :
    (Finset.range (n + 1)).sum (fun t =>
        halfTsallisPotentialValue arms (eta t)
            (FTRL.cumulativeLoss loss t)
            (halfTsallisScheduledMinimizer arms harms eta loss t) -
          halfTsallisPotentialValue arms (eta t)
            (FTRL.cumulativeLoss loss (t + 1))
            (halfTsallisScheduledSameRateNext arms harms eta loss t) -
          FTRL.linearLoss arms q (loss t)) <=
      (halfTsallisPotentialMass arms
          (halfTsallisScheduledMinimizer arms harms eta loss 0) -
        halfTsallisPotentialMass arms q) / eta n := by
  apply sum_halfTsallisScheduledPotentialPenalty_le_initial_sub_comparator_div
    arms eta loss
      (halfTsallisScheduledMinimizer arms harms eta loss)
      (halfTsallisScheduledSameRateNext arms harms eta loss)
      q n heta hetaMono
  · intro t _ht
    exact halfTsallisMinimizer_isRegularizedMinimizer
      arms harms (eta t) (FTRL.cumulativeLoss loss t)
  · intro t _ht
    exact halfTsallisMinimizer_isRegularizedMinimizer
      arms harms (eta t) (FTRL.cumulativeLoss loss (t + 1))
  · exact hq

/-- Best-arm specialization retaining the explicit terminal `-1 / eta n`
contribution encoded by the point-mass comparator. -/
theorem sum_halfTsallisCanonicalScheduledPotentialPenalty_pointMass_le
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real) (loss : Nat -> Action -> Real)
    {best : Action} (hbest : best ∈ arms) (n : Nat)
    (heta : forall t, t <= n -> 0 < eta t)
    (hetaMono : forall t, t < n -> eta (t + 1) <= eta t) :
    (Finset.range (n + 1)).sum (fun t =>
        halfTsallisPotentialValue arms (eta t)
            (FTRL.cumulativeLoss loss t)
            (halfTsallisScheduledMinimizer arms harms eta loss t) -
          halfTsallisPotentialValue arms (eta t)
            (FTRL.cumulativeLoss loss (t + 1))
            (halfTsallisScheduledSameRateNext arms harms eta loss t) -
          FTRL.linearLoss arms (pointMass best) (loss t)) <=
      halfTsallisPotentialMass arms
          (halfTsallisScheduledMinimizer arms harms eta loss 0) / eta n -
        1 / eta n := by
  simpa [halfTsallisPotentialMass_pointMass arms hbest, sub_div] using
    sum_halfTsallisCanonicalScheduledPotentialPenalty_le
      arms harms eta loss (pointMass best) n heta hetaMono
        (finiteSimplex_pointMass arms hbest)

end Tsallis
end BanditRLProof
