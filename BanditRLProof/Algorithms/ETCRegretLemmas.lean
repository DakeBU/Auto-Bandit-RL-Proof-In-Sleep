import BanditRLProof.RegretCountBounds
import BanditRLProof.Algorithms.ETCTraceCountLemmas

/-!
# Deterministic ETC regret lemmas

This module contains ETC-specific deterministic regret scaffolds.  It consumes
the round-robin exploration count layer and deliberately stays below commit
behavior, empirical means, probability, concentration, and final ETC regret
theorems.
-/

namespace BanditRLProof

/--
The pseudo-regret of the pure round-robin ETC exploration prefix is bounded by
the sum of arm gaps times the configured number of exploration pulls per arm.

This is the `ETC-EXPLORATION-REGRET-BOUND` project-local deterministic regret
scaffold.
-/
theorem ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K) :
    pseudoRegret model (ETC.exploreArm spec) (spec.explorationPulls * K) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) := by
  exact
    pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound
      (model := model)
      (action := ETC.exploreArm spec)
      (n := spec.explorationPulls * K)
      (B := spec.explorationPulls)
      (hB := by
        intro a
        exact le_of_eq
          (ETC.pullCount_exploreArm_explorationPulls_mul_K_eq spec a))

/--
The pseudo-regret of the fixed-commit ETC trace at the exploration horizon is
bounded by the sum of arm gaps times the configured number of exploration pulls
per arm.

This is the `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND`
project-local deterministic regret scaffold.
-/
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K) (commitArm : Fin K) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) := by
  exact
    pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound
      (model := model)
      (action := ETC.actionWithCommit spec commitArm)
      (n := spec.explorationPulls * K)
      (B := spec.explorationPulls)
      (hB := by
        intro a
        exact le_of_eq
          (ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
            (spec := spec)
            (commitArm := commitArm)
            (a := a)))

/--
The fixed-commit ETC trace at an exploration horizon plus suffix `r` is bounded
by the gap-weighted count budget that allocates `explorationPulls` to every arm
and the suffix budget only to the committed arm.

This is the `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET` project-local
deterministic regret scaffold.  It deliberately keeps the right-hand side in
the unsimplified per-arm budget form.
-/
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_suffix_count_budget
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K =>
          model.gap a *
            (((spec.explorationPulls +
                (if commitArm = a then r else 0) : Nat) : Rat))) := by
  exact
    pseudoRegret_le_finset_sum_gap_mul_nat_count_bound
      (model := model)
      (action := ETC.actionWithCommit spec commitArm)
      (n := spec.explorationPulls * K + r)
      (B := fun a : Fin K =>
        spec.explorationPulls + (if commitArm = a then r else 0))
      (hB := by
        intro a
        exact le_of_eq
          (ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
            (spec := spec)
            (commitArm := commitArm)
            (a := a)
            (r := r)))

/--
The fixed-commit ETC trace after an exploration horizon plus suffix `r` also
satisfies the coarser uniform count-budget regret bound where every arm is
allowed `explorationPulls + r` pulls.

This is the `ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND`
project-local deterministic regret scaffold.
-/
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        ((((spec.explorationPulls + r : Nat) : Rat))) := by
  exact
    pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound
      (model := model)
      (action := ETC.actionWithCommit spec commitArm)
      (n := spec.explorationPulls * K + r)
      (B := spec.explorationPulls + r)
      (hB := by
        intro a
        rw [ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
          (spec := spec)
          (commitArm := commitArm)
          (a := a)
          (r := r)]
        apply Nat.add_le_add_left
        by_cases h : commitArm = a
        · simp [h]
        · simp [h])

/--
The fixed-commit ETC trace splits pseudo-regret after the exploration horizon
into the exploration-horizon pseudo-regret plus one committed-arm gap for each
suffix pull.

This is the `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET` project-local
deterministic regret scaffold.
-/
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) =
      pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K) +
        (((r : Nat) : Rat) * model.gap commitArm) := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      have hge :
          spec.explorationPulls * K <= spec.explorationPulls * K + r := by
        exact Nat.le_add_right (spec.explorationPulls * K) r
      have hact :
          ETC.actionWithCommit spec commitArm
              (spec.explorationPulls * K + r) = commitArm :=
        ETC.actionWithCommit_eq_commitArm_of_ge
          (spec := spec)
          (commitArm := commitArm)
          (t := spec.explorationPulls * K + r)
          hge
      rw [Nat.add_succ]
      rw [pseudoRegret_succ, hact, ih]
      rw [Nat.cast_succ, add_mul, one_mul, add_assoc]

/--
If the fixed commit arm is the model's selected best arm, extending the ETC
trace past the exploration horizon adds no pseudo-regret.

This is the `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET` project-local
deterministic regret scaffold.
-/
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_of_commitArm_eq_bestArm
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat)
    (hcommit : commitArm = model.bestArm) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) =
      pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K) := by
  rw [ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
    (spec := spec)
    (model := model)
    (commitArm := commitArm)
    (r := r)]
  rw [hcommit]
  simp [FiniteBanditModel.gap_bestArm]

/--
If the fixed commit arm is the model's selected best arm, the ETC regret after
any post-exploration suffix is bounded by the exploration-horizon regret
budget.

This is the `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND`
project-local deterministic regret scaffold.
-/
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_of_commitArm_eq_bestArm
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat)
    (hcommit : commitArm = model.bestArm) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) := by
  rw [ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_of_commitArm_eq_bestArm
    (spec := spec)
    (model := model)
    (commitArm := commitArm)
    (r := r)
    (hcommit := hcommit)]
  exact
    ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
      (spec := spec)
      (model := model)
      (commitArm := commitArm)

/--
The phase-split equality and the exploration-horizon regret bound combine into
a deterministic fixed-commit ETC regret bound with an explicit committed-arm
suffix term.

This is the `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND`
project-local deterministic regret scaffold.
-/
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix_gap
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) +
      (((r : Nat) : Rat) * model.gap commitArm) := by
  rw [ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
    (spec := spec)
    (model := model)
    (commitArm := commitArm)
    (r := r)]
  exact
    add_le_add
      (ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
        (spec := spec)
        (model := model)
        (commitArm := commitArm))
      (le_refl ((((r : Nat) : Rat) * model.gap commitArm)))

end BanditRLProof
