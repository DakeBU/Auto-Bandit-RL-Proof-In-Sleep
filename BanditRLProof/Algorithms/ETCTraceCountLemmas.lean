import BanditRLProof.LeafLemmas
import BanditRLProof.Algorithms.ETCTrace
import BanditRLProof.Algorithms.ETCCountLemmas

/-!
# ETC phase-switching trace count lemmas

This module contains deterministic pull-count facts for the fixed-commit ETC
trace.  It stays below regret, empirical commit selection, probability, and
concentration.
-/

namespace BanditRLProof

/--
On any prefix contained inside the configured exploration horizon, the
fixed-commit ETC trace has the same pull counts as the pure round-robin
exploration trace.

This is the `ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT` project-local
trace/count transfer leaf.
-/
theorem ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (n : Nat) (hn : n <= spec.explorationPulls * K) :
    pullCount (ETC.actionWithCommit spec commitArm) a n =
      pullCount (ETC.exploreArm spec) a n := by
  revert hn
  induction n with
  | zero =>
      intro _hn
      simp [pullCount]
  | succ n ih =>
      intro hn
      have hn_le : n <= spec.explorationPulls * K :=
        Nat.le_trans (Nat.le_succ n) hn
      have hn_lt : n < spec.explorationPulls * K :=
        Nat.lt_of_succ_le hn
      have hact :
          ETC.actionWithCommit spec commitArm n = ETC.exploreArm spec n :=
        ETC.actionWithCommit_eq_exploreArm_of_lt spec commitArm hn_lt
      rw [pullCount_succ, pullCount_succ]
      rw [ih hn_le]
      rw [hact]

/--
At the configured exploration horizon, the fixed-commit ETC trace has pulled
each arm exactly `spec.explorationPulls` times.

This is the `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT` project-local
trace/count adapter.
-/
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K) =
      spec.explorationPulls := by
  calc
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K)
        = pullCount (ETC.exploreArm spec) a (spec.explorationPulls * K) := by
            exact
              ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le
                spec commitArm a (spec.explorationPulls * K) (Nat.le_refl _)
    _ = spec.explorationPulls := by
            exact ETC.pullCount_exploreArm_explorationPulls_mul_K_eq spec a

/--
At the configured exploration horizon, every arm in the fixed-commit ETC trace
has a positive pull count whenever the configured number of exploration pulls
is positive.

This is the first denominator-positivity leaf for future empirical-mean
construction.  It stays purely deterministic and Nat-valued.
-/
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    0 < pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) := by
  have hcount :
      pullCount (ETC.actionWithCommit spec commitArm) a
          (spec.explorationPulls * K) =
        spec.explorationPulls :=
    ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
      spec commitArm a
  simpa [hcount] using hexplorationPulls_pos

/--
Rat-cast form of the fixed-commit ETC exploration pull-count positivity leaf.

This is the first denominator adapter for future Rat-valued empirical means.
It only transports the compiled Nat positivity theorem across the Nat-to-Rat
cast.
-/
theorem ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    (0 : Rat) < (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat) := by
  have hnat :
      0 < pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K) :=
    ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos
      spec commitArm a hexplorationPulls_pos
  exact_mod_cast hnat

/--
Nonzero Rat-denominator form of the fixed-commit ETC exploration pull-count
positivity leaf.

This is still only a deterministic denominator adapter.  It does not define
empirical means or introduce probability assumptions.
-/
theorem ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    Not ((pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat) = 0) := by
  have hpos :
      (0 : Rat) < (pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K) : Rat) :=
    ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos
      spec commitArm a hexplorationPulls_pos
  exact ne_of_gt hpos

/--
After the configured exploration horizon, one step of the fixed-commit ETC
trace updates pull counts according to whether the queried arm is the commit
arm.

This is the `ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT` project-local
trace/count update leaf.
-/
theorem ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) {t : Nat}
    (ht : spec.explorationPulls * K <= t) :
    pullCount (ETC.actionWithCommit spec commitArm) a (Nat.succ t) =
      pullCount (ETC.actionWithCommit spec commitArm) a t +
        if commitArm = a then 1 else 0 := by
  rw [pullCount_succ]
  have hact :
      ETC.actionWithCommit spec commitArm t = commitArm :=
    ETC.actionWithCommit_eq_commitArm_of_ge spec commitArm ht
  simp [hact]

/--
After the configured exploration horizon, the fixed-commit ETC trace has a
closed-form pull count: the commit arm receives every suffix pull, while all
other arms keep their exploration-horizon count.

This is the `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` project-local trace/count
closed-form leaf.
-/
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K + r) =
      spec.explorationPulls + (if commitArm = a then r else 0) := by
  induction r with
  | zero =>
      simp [ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq]
  | succ r ih =>
      have hge :
          spec.explorationPulls * K <= spec.explorationPulls * K + r :=
        Nat.le_add_right (spec.explorationPulls * K) r
      have hstep :
          pullCount (ETC.actionWithCommit spec commitArm) a
              (Nat.succ (spec.explorationPulls * K + r)) =
            pullCount (ETC.actionWithCommit spec commitArm) a
                (spec.explorationPulls * K + r) +
              if commitArm = a then 1 else 0 :=
        ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge
          (spec := spec)
          (commitArm := commitArm)
          (a := a)
          (t := spec.explorationPulls * K + r)
          hge
      rw [Nat.add_succ]
      rw [hstep]
      rw [ih]
      by_cases h : commitArm = a
      · simp [h, Nat.add_assoc]
      · simp [h]

/--
After the configured exploration horizon, every non-commit arm keeps its
exploration-horizon pull count.

This is the `ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT` project-local
trace/count corollary.
-/
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_of_ne
    {K : Nat} (spec : ETC.Spec K) {commitArm a : Fin K}
    (hne : commitArm ≠ a) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K + r) =
      spec.explorationPulls := by
  simpa [hne] using
    ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
      spec commitArm a r

/--
After the configured exploration horizon, the commit arm has the exploration
count plus every suffix pull.

This is the `ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT` project-local
trace/count corollary.
-/
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_commitArm
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) commitArm
        (spec.explorationPulls * K + r) =
      spec.explorationPulls + r := by
  simpa using
    ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
      spec commitArm commitArm r

end BanditRLProof
