import BanditRLProof.TsallisRefinedImportanceWeightedMoment
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Obstruction to refining the current symmetrized half-Tsallis stability term

The shifted ordinary-importance-weighted moments have the paper-shaped
sampled-action average, but the current local stability quantity
`<p - p_next, hatLoss>` is not the conjugate-potential stability used in the
Tsallis-INF proof.  This module gives a fully rational two-arm counterexample:
the current and sampled-update distributions are strict simplex minimizers and
the losses lie in `[0,1]`, yet the proposed refined averaged upper bound fails.

The counterexample closes the direct averaged-stability diagnostic.  It does
not obstruct the paper's conjugate-potential route.
-/

namespace BanditRLProof
namespace Tsallis

private abbrev CounterAction := Fin 2

private noncomputable def counterArms : Finset CounterAction := Finset.univ

private noncomputable def counterEta : Real := 1 / 100

private noncomputable def counterProb : CounterAction -> Real := fun action =>
  if action = 0 then 49 / 625 else 576 / 625

private noncomputable def counterScore : CounterAction -> Real := fun action =>
  if action = 0 then 2500 / 7 else 625 / 6

private noncomputable def counterLoss : CounterAction -> Real := fun action =>
  if action = 0 then 5761809344308787 / 5762453410125000
  else 27075525128016 / 30555867765625

private noncomputable def counterNext
    (chosen action : CounterAction) : Real :=
  if chosen = 0 then
    if action = 0 then 1813828968643041 / 24778200568643041
    else 22964371600000000 / 24778200568643041
  else
    if action = 0 then 120121402720081 / 1524122302720081
    else 1404000900000000 / 1524122302720081

private noncomputable def counterNextMultiplier
    (chosen : CounterAction) : Real :=
  if chosen = 0 then 1329713 / 454620000 else 14688 / 1565713

private theorem sqrt_49 : Real.sqrt (49 : Real) = 7 := by
  rw [show (49 : Real) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private theorem sqrt_576 : Real.sqrt (576 : Real) = 24 := by
  rw [show (576 : Real) = 24 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private theorem sqrt_625 : Real.sqrt (625 : Real) = 25 := by
  rw [show (625 : Real) = 25 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private theorem sqrt_24778200568643041 :
    Real.sqrt (24778200568643041 : Real) = 157410929 := by
  rw [show (24778200568643041 : Real) = 157410929 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

private theorem sqrt_1813828968643041 :
    Real.sqrt (1813828968643041 : Real) = 42589071 := by
  rw [show (1813828968643041 : Real) = 42589071 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

private theorem sqrt_22964371600000000 :
    Real.sqrt (22964371600000000 : Real) = 151540000 := by
  rw [show (22964371600000000 : Real) = 151540000 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

private theorem sqrt_1524122302720081 :
    Real.sqrt (1524122302720081 : Real) = 39040009 := by
  rw [show (1524122302720081 : Real) = 39040009 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

private theorem sqrt_120121402720081 :
    Real.sqrt (120121402720081 : Real) = 10959991 := by
  rw [show (120121402720081 : Real) = 10959991 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

private theorem sqrt_1404000900000000 :
    Real.sqrt (1404000900000000 : Real) = 37470000 := by
  rw [show (1404000900000000 : Real) = 37470000 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

private theorem counterEta_pos : 0 < counterEta := by
  norm_num [counterEta]

private theorem counterEta_le_one : counterEta <= 1 := by
  norm_num [counterEta]

private theorem counterProb_simplex :
    FTRL.finiteSimplex counterArms counterProb := by
  constructor
  · intro action _haction
    fin_cases action <;> norm_num [counterProb]
  · norm_num [counterArms, counterProb, Fin.sum_univ_two]

private theorem counterProb_pos
    (action : CounterAction) (haction : action ∈ counterArms) :
    0 < counterProb action := by
  fin_cases action <;> norm_num [counterProb]

private theorem counterLoss_mem_Icc
    (action : CounterAction) (haction : action ∈ counterArms) :
    0 <= counterLoss action ∧ counterLoss action <= 1 := by
  fin_cases action <;> norm_num [counterLoss]

private theorem counterNext_simplex
    (chosen : CounterAction) (hchosen : chosen ∈ counterArms) :
    FTRL.finiteSimplex counterArms (counterNext chosen) := by
  constructor
  · intro action _haction
    fin_cases chosen <;> fin_cases action <;> norm_num [counterNext]
  · fin_cases chosen <;>
      norm_num [counterArms, counterNext, Fin.sum_univ_two]

private theorem counterNext_pos
    (chosen : CounterAction) (hchosen : chosen ∈ counterArms)
    (action : CounterAction) (haction : action ∈ counterArms) :
    0 < counterNext chosen action := by
  fin_cases chosen <;> fin_cases action <;> norm_num [counterNext]

private theorem rpow_neg_half_eq_inv_sqrt {x : Real} (hx : 0 < x) :
    x ^ (-(1 / 2 : Real)) = 1 / Real.sqrt x := by
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  simp [one_div]

private theorem counterProb_stationary :
    HalfTsallisInteriorStationary counterArms counterEta counterScore
      counterProb 0 := by
  intro action haction
  rw [rpow_neg_half_eq_inv_sqrt (counterProb_pos action haction)]
  fin_cases action <;>
    norm_num [counterEta, counterScore, counterProb, sqrt_49,
      sqrt_576, sqrt_625]

private theorem counterNext_stationary
    (chosen : CounterAction) (hchosen : chosen ∈ counterArms) :
    HalfTsallisInteriorStationary counterArms counterEta
      (fun action => counterScore action +
        Exp3.importanceWeightedLoss counterProb counterLoss chosen action)
      (counterNext chosen) (counterNextMultiplier chosen) := by
  intro action haction
  rw [rpow_neg_half_eq_inv_sqrt
    (counterNext_pos chosen hchosen action haction)]
  fin_cases chosen <;> fin_cases action <;>
    norm_num [counterArms, counterEta, counterScore, counterProb, counterLoss,
      counterNext, counterNextMultiplier, Exp3.importanceWeightedLoss,
      sqrt_49, sqrt_576, sqrt_625, sqrt_24778200568643041,
      sqrt_1813828968643041, sqrt_22964371600000000,
      sqrt_1524122302720081, sqrt_120121402720081,
      sqrt_1404000900000000]

private theorem counterProb_minimizer :
    FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex counterArms)
      counterArms counterEta (negEntropyRegularizer counterArms (1 / 2 : Real))
      counterScore counterProb := by
  exact isRegularizedMinimizer_of_halfTsallisInteriorStationary
    counterArms counterEta counterScore counterProb 0 counterProb_simplex
    counterProb_pos counterProb_stationary

private theorem counterNext_minimizer
    (chosen : CounterAction) (hchosen : chosen ∈ counterArms) :
    FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex counterArms)
      counterArms counterEta (negEntropyRegularizer counterArms (1 / 2 : Real))
      (fun action => counterScore action +
        Exp3.importanceWeightedLoss counterProb counterLoss chosen action)
      (counterNext chosen) := by
  exact isRegularizedMinimizer_of_halfTsallisInteriorStationary
    counterArms counterEta
    (fun action => counterScore action +
      Exp3.importanceWeightedLoss counterProb counterLoss chosen action)
    (counterNext chosen) (counterNextMultiplier chosen)
    (counterNext_simplex chosen hchosen)
    (counterNext_pos chosen hchosen)
    (counterNext_stationary chosen hchosen)

/--
Even with strict positive simplex minimizers and `[0,1]` losses, the current
sampled-action average of `<p - p_next, hatLoss>` can exceed the locally scaled
paper coefficient `eta * sum sqrt(p) * (1-p) + 2 * eta^2`.
-/
theorem exists_minimizer_counterexample_to_refinedAveragedStability :
    ∃ (eta : Real) (score prob loss : Fin 2 -> Real)
      (next : Fin 2 -> Fin 2 -> Real),
      0 < eta ∧
      eta <= 1 ∧
      FTRL.finiteSimplex Finset.univ prob ∧
      (∀ action ∈ (Finset.univ : Finset (Fin 2)), 0 < prob action) ∧
      (∀ action ∈ (Finset.univ : Finset (Fin 2)),
        0 <= loss action ∧ loss action <= 1) ∧
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex Finset.univ)
        Finset.univ eta (negEntropyRegularizer Finset.univ (1 / 2 : Real))
        score prob ∧
      (∀ chosen ∈ (Finset.univ : Finset (Fin 2)),
        ∀ action ∈ (Finset.univ : Finset (Fin 2)),
          0 < next chosen action) ∧
      (∀ chosen ∈ (Finset.univ : Finset (Fin 2)),
        FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex Finset.univ)
          Finset.univ eta (negEntropyRegularizer Finset.univ (1 / 2 : Real))
          (fun action => score action +
            Exp3.importanceWeightedLoss prob loss chosen action)
          (next chosen)) ∧
      eta * (Finset.univ : Finset (Fin 2)).sum (fun action =>
          Real.sqrt (prob action) * (1 - prob action)) + 2 * eta ^ 2 <
        (Finset.univ : Finset (Fin 2)).sum (fun chosen =>
          prob chosen *
            (FTRL.linearLoss Finset.univ prob
                (Exp3.importanceWeightedLoss prob loss chosen) -
              FTRL.linearLoss Finset.univ (next chosen)
                (Exp3.importanceWeightedLoss prob loss chosen))) := by
  refine ⟨counterEta, counterScore, counterProb, counterLoss, counterNext,
    counterEta_pos, counterEta_le_one, counterProb_simplex, counterProb_pos,
    counterLoss_mem_Icc, counterProb_minimizer, counterNext_pos,
    counterNext_minimizer, ?_⟩
  norm_num [counterArms, counterEta, counterProb, counterLoss, counterNext,
    FTRL.linearLoss, Exp3.importanceWeightedLoss, Fin.sum_univ_two,
    sqrt_49, sqrt_576, sqrt_625]

end Tsallis
end BanditRLProof
