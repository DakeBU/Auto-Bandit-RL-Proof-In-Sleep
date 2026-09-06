import BanditRLProof.Core
import BanditRLProof.Algorithms.ETC

/-!
# ETC phase-switching traces

This module introduces the first deterministic boundary for phase-switching
Explore-Then-Commit traces.  The commit arm is supplied explicitly; empirical
mean selection, probability, concentration, and regret facts live in later
leaves.
-/

namespace BanditRLProof
namespace ETC

/-- Explore by round-robin until the configured horizon, then play `commitArm`. -/
def actionWithCommit {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) :
    ActionTrace (Fin K) :=
  fun t : Nat =>
    if t < spec.explorationPulls * K then
      ETC.exploreArm spec t
    else
      commitArm

/--
During the configured exploration prefix, the phase-switching ETC trace agrees
with the pure round-robin exploration trace.

This is the `ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE` project-local trace-boundary
leaf.
-/
@[simp] theorem actionWithCommit_eq_exploreArm_of_lt
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : t < spec.explorationPulls * K) :
    ETC.actionWithCommit spec commitArm t = ETC.exploreArm spec t := by
  simp [ETC.actionWithCommit, h]

/--
After the configured exploration prefix, the phase-switching ETC trace plays
the supplied commit arm.

This is the `ETC-ACTION-WITH-COMMIT-COMMIT-PHASE` project-local trace-boundary
leaf.
-/
@[simp] theorem actionWithCommit_eq_commitArm_of_ge
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : spec.explorationPulls * K <= t) :
    ETC.actionWithCommit spec commitArm t = commitArm := by
  have hnot : ¬ t < spec.explorationPulls * K := Nat.not_lt_of_ge h
  simp [ETC.actionWithCommit, hnot]

/--
After the configured exploration prefix, if the supplied commit arm is the
model's selected best arm, the phase-switching ETC trace plays that best arm.

This is the `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE` project-local
trace-boundary leaf.
-/
theorem actionWithCommit_eq_bestArm_of_commitArm_eq_bestArm_of_explorationPulls_mul_K_le
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (t : Nat)
    (hcommit : commitArm = model.bestArm)
    (ht : spec.explorationPulls * K <= t) :
    ETC.actionWithCommit spec commitArm t = model.bestArm := by
  rw [ETC.actionWithCommit_eq_commitArm_of_ge
    (spec := spec)
    (commitArm := commitArm)
    (t := t)
    ht]
  exact hcommit

end ETC
end BanditRLProof
