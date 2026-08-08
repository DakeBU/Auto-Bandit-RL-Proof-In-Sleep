import BanditRLProof.TsallisSelfBounding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Refined half-Tsallis stability to suboptimal-arm budgets

The paper's refined stability term contains
`sum_a sqrt (p a) * (1 - p a)`.  This module proves the finite-simplex
elimination of one optimal arm and connects that bound to the compiled
self-bounding completion-of-squares consumer.

Producing the refined all-arm stability bound from the generated algorithm is
separate: it requires the conjugate-potential stability estimate and the
time-varying penalty route, rather than the existing fixed-learning-rate
`<p_t - p_(t+1), hatLoss_t>` upper bound.
-/

namespace BanditRLProof
namespace Tsallis

universe u v

theorem probability_le_sqrt
    (probability : Real) (hprobability : 0 <= probability)
    (hprobability_le_one : probability <= 1) :
    probability <= Real.sqrt probability := by
  apply (Real.le_sqrt hprobability hprobability).2
  nlinarith

theorem sqrt_mul_one_sub_le_sqrt
    (probability : Real) (hprobability : 0 <= probability) :
    Real.sqrt probability * (1 - probability) <=
      Real.sqrt probability := by
  have hsqrtNonneg : 0 <= Real.sqrt probability := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hsqrtNonneg hprobability]

theorem sqrt_mul_one_sub_le_one_sub
    (probability : Real) (hprobability_le_one : probability <= 1) :
    Real.sqrt probability * (1 - probability) <= 1 - probability := by
  have hsqrtLeOne : Real.sqrt probability <= 1 :=
    (Real.sqrt_le_one).2 hprobability_le_one
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hsqrtLeOne
      (sub_nonneg.mpr hprobability_le_one)

theorem one_sub_eq_sum_erase
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {best : Action} (hbest : best ∈ arms)
    (probability : Action -> Real)
    (hprobability : FTRL.finiteSimplex arms probability) :
    1 - probability best =
      (arms.erase best).sum probability := by
  have hsplit := Finset.add_sum_erase arms probability hbest
  rw [hprobability.2] at hsplit
  linarith

/-- Eliminate one distinguished arm from the paper's refined half-power
stability budget. -/
theorem sum_sqrt_mul_one_sub_le_two_mul_sum_erase_sqrt
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {best : Action} (hbest : best ∈ arms)
    (probability : Action -> Real)
    (hprobability : FTRL.finiteSimplex arms probability) :
    arms.sum (fun action =>
        Real.sqrt (probability action) * (1 - probability action)) <=
      2 * (arms.erase best).sum (fun action =>
        Real.sqrt (probability action)) := by
  have hbestUpper :
      Real.sqrt (probability best) * (1 - probability best) <=
        (arms.erase best).sum probability := by
    rw [← one_sub_eq_sum_erase arms hbest probability hprobability]
    exact sqrt_mul_one_sub_le_one_sub
      (probability best) (finiteSimplex_apply_le_one hprobability hbest)
  have heraseUpper :
      (arms.erase best).sum (fun action =>
          Real.sqrt (probability action) * (1 - probability action)) <=
        (arms.erase best).sum (fun action => Real.sqrt (probability action)) := by
    apply Finset.sum_le_sum
    intro action haction
    exact sqrt_mul_one_sub_le_sqrt
      (probability action)
      (hprobability.1 action (Finset.mem_of_mem_erase haction))
  have hprobToSqrt :
      (arms.erase best).sum probability <=
        (arms.erase best).sum (fun action => Real.sqrt (probability action)) := by
    apply Finset.sum_le_sum
    intro action haction
    have hairm : action ∈ arms := Finset.mem_of_mem_erase haction
    exact probability_le_sqrt
      (probability action) (hprobability.1 action hairm)
      (finiteSimplex_apply_le_one hprobability hairm)
  rw [← Finset.add_sum_erase arms
    (fun action => Real.sqrt (probability action) *
      (1 - probability action)) hbest]
  linarith

/-- A finite time-by-suboptimal-arm consumer for the paper-shaped refined
stability budget.  The remaining algorithmic obligation is exactly `hupper`. -/
theorem regret_le_of_refinedHalfPowerSelfBounding
    {Time : Type u} {Action : Type v}
    [DecidableEq Time] [DecidableEq Action]
    (times : Finset Time) (arms : Finset Action)
    {best : Action} (hbest : best ∈ arms)
    (probability : Time -> Action -> Real)
    (coefficient : Time -> Real) (gap : Action -> Real)
    (regret base corruption : Real)
    (hprobability : ∀ time ∈ times,
      FTRL.finiteSimplex arms (probability time))
    (hcoefficient : ∀ time ∈ times, 0 <= coefficient time)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (hselfBounding :
      times.sum (fun time => (arms.erase best).sum (fun action =>
          gap action * probability time action)) - corruption <= regret)
    (hupper :
      regret <= base + times.sum (fun time =>
        coefficient time * arms.sum (fun action =>
          Real.sqrt (probability time action) *
            (1 - probability time action)))) :
    regret <=
      2 * base +
        (times.product (arms.erase best)).sum (fun index =>
          (2 * coefficient index.1) ^ 2 / gap index.2) +
        corruption := by
  let indices := times.product (arms.erase best)
  have hprobabilityIndex : ∀ index ∈ indices,
      0 <= probability index.1 index.2 := by
    intro index hindex
    have htime : index.1 ∈ times := (Finset.mem_product.mp hindex).1
    have hactionErase : index.2 ∈ arms.erase best :=
      (Finset.mem_product.mp hindex).2
    exact (hprobability index.1 htime).1 index.2
      (Finset.mem_of_mem_erase hactionErase)
  have hgapIndex : ∀ index ∈ indices, 0 < gap index.2 := by
    intro index hindex
    exact hgap index.2 (Finset.mem_product.mp hindex).2
  have hselfBoundingIndex :
      indices.sum (fun index =>
          gap index.2 * probability index.1 index.2) - corruption <= regret := by
    simpa [indices, Finset.sum_product] using hselfBounding
  have hrefined :
      times.sum (fun time =>
          coefficient time * arms.sum (fun action =>
            Real.sqrt (probability time action) *
              (1 - probability time action))) <=
        times.sum (fun time =>
          2 * coefficient time * (arms.erase best).sum (fun action =>
            Real.sqrt (probability time action))) := by
    apply Finset.sum_le_sum
    intro time htime
    have htimeBound :=
      sum_sqrt_mul_one_sub_le_two_mul_sum_erase_sqrt
        arms hbest (probability time) (hprobability time htime)
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left htimeBound (hcoefficient time htime)
  have hupperIndex :
      regret <= base + indices.sum (fun index =>
        (2 * coefficient index.1) *
          Real.sqrt (probability index.1 index.2)) := by
    calc
      regret <= base + times.sum (fun time =>
          coefficient time * arms.sum (fun action =>
            Real.sqrt (probability time action) *
              (1 - probability time action))) := hupper
      _ <= base + times.sum (fun time =>
          2 * coefficient time * (arms.erase best).sum (fun action =>
            Real.sqrt (probability time action))) :=
        by simpa [add_comm] using add_le_add_left hrefined base
      _ = base + indices.sum (fun index =>
          (2 * coefficient index.1) *
            Real.sqrt (probability index.1 index.2)) := by
        simp [indices, Finset.sum_product, Finset.mul_sum, mul_assoc]
  exact regret_le_two_mul_base_add_sum_sq_div_gap_add_corruption
    indices
    (fun index => probability index.1 index.2)
    (fun index => 2 * coefficient index.1)
    (fun index => gap index.2)
    regret base corruption hprobabilityIndex hgapIndex
      hselfBoundingIndex hupperIndex

end Tsallis
end BanditRLProof
