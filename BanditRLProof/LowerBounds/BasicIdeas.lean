import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith

/-!
# Lower bounds: basic ideas

This module formalizes the semantic and deterministic interfaces developed in
Lattimore--Szepesvári, *Bandit Algorithms* (2020), Part IV, Chapter 13.

The source states its finite-arm Gaussian minimax theorem in Chapter 13 but
defers the proof to Chapter 15. Accordingly, this module does **not** claim
that theorem. It provides the worst-case/minimax order surface, the
least-explored alternative-arm averaging leaf, and the conditional algebra
behind the chapter's two-environment heuristic. The cross-environment
information comparison remains an explicit premise for Chapters 14--15.
-/

namespace BanditRLProof
namespace LowerBounds

open scoped BigOperators ENNReal

universe u v

/--
Worst-case expected regret of one policy over an explicit environment class.

The `ENNReal` codomain supplies the source-level supremum without a hidden
boundedness hypothesis. If `environmentClass` is empty, this retains the
standard complete-lattice value `bot`; meaningful bandit consumers should
prove their intended class is nonempty.
-/
noncomputable def worstCaseExpectedRegret
    {Policy : Type u} {Environment : Type v}
    (regret : Policy -> Environment -> ENNReal)
    (environmentClass : Set Environment)
    (policy : Policy) : ENNReal :=
  ⨆ environment : environmentClass, regret policy environment.1

/--
Minimax expected regret over explicit policy and environment classes.

The definition mirrors `inf_pi sup_nu R_n(pi,nu)`. Nonemptiness of the classes
is intentionally a consumer-side semantic contract rather than a hidden
assumption of the definition.
-/
noncomputable def minimaxExpectedRegret
    {Policy : Type u} {Environment : Type v}
    (regret : Policy -> Environment -> ENNReal)
    (policyClass : Set Policy)
    (environmentClass : Set Environment) : ENNReal :=
  ⨅ policy : policyClass,
    worstCaseExpectedRegret regret environmentClass policy.1

/-- One environment's regret is below the worst case over any class containing it. -/
theorem expectedRegret_le_worstCaseExpectedRegret
    {Policy : Type u} {Environment : Type v}
    (regret : Policy -> Environment -> ENNReal)
    (environmentClass : Set Environment)
    (policy : Policy) (environment : Environment)
    (henvironment : environment ∈ environmentClass) :
    regret policy environment ≤
      worstCaseExpectedRegret regret environmentClass policy := by
  unfold worstCaseExpectedRegret
  exact le_iSup (fun member : environmentClass => regret policy member.1)
    ⟨environment, henvironment⟩

/-- The minimax value is below the worst-case value of each admissible policy. -/
theorem minimaxExpectedRegret_le_worstCaseExpectedRegret
    {Policy : Type u} {Environment : Type v}
    (regret : Policy -> Environment -> ENNReal)
    (policyClass : Set Policy) (environmentClass : Set Environment)
    (policy : Policy) (hpolicy : policy ∈ policyClass) :
    minimaxExpectedRegret regret policyClass environmentClass ≤
      worstCaseExpectedRegret regret environmentClass policy := by
  unfold minimaxExpectedRegret
  exact iInf_le_of_le ⟨policy, hpolicy⟩ le_rfl

/-- A uniform lower bound on every admissible policy is a minimax lower bound. -/
theorem le_minimaxExpectedRegret
    {Policy : Type u} {Environment : Type v}
    (regret : Policy -> Environment -> ENNReal)
    (policyClass : Set Policy) (environmentClass : Set Environment)
    (lower : ENNReal)
    (hlower : ∀ policy : policyClass,
      lower ≤ worstCaseExpectedRegret regret environmentClass policy.1) :
    lower ≤ minimaxExpectedRegret regret policyClass environmentClass := by
  unfold minimaxExpectedRegret
  exact le_iInf hlower

/--
Finite averaging: among a nonempty family whose sum is at most `budget`, one
coordinate is at most `budget / m`.

This is a Mathlib-composed deterministic leaf. It contains no bandit law,
expectation, measurability, or concentration assumption.
-/
theorem exists_alternative_le_average
    {m : Nat} (hm : 0 < m)
    (alternativeExpectedPulls : Fin m -> Real)
    (budget : Real)
    (hbudget : ∑ i : Fin m, alternativeExpectedPulls i ≤ budget) :
    ∃ i : Fin m,
      alternativeExpectedPulls i ≤ budget / (m : Real) := by
  haveI : Nonempty (Fin m) := Fintype.card_pos_iff.mp (by simpa using hm)
  have huniv : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty
  have hmReal : (m : Real) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hconstant :
      (∑ _i : Fin m, budget / (m : Real)) = budget := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_div_cancel₀ budget hmReal
  have hcompare :
      (∑ i : Fin m, alternativeExpectedPulls i) ≤
        ∑ _i : Fin m, budget / (m : Real) := by
    simpa [hconstant] using hbudget
  obtain ⟨i, _hi, hile⟩ :=
    Finset.exists_le_of_sum_le huniv hcompare
  exact ⟨i, hile⟩

/--
Removing the distinguished arm zero from an exact nonnegative pull budget
leaves at most the full budget on the `Fin.succ` alternative arms.
-/
theorem alternativeExpectedPullBudget_le
    {m : Nat}
    (expectedPulls : Fin (m + 1) -> Real)
    (budget : Real)
    (hnonneg : ∀ arm, 0 ≤ expectedPulls arm)
    (htotal : ∑ arm : Fin (m + 1), expectedPulls arm = budget) :
    (∑ i : Fin m, expectedPulls i.succ) ≤ budget := by
  rw [Fin.sum_univ_succ] at htotal
  nlinarith [hnonneg (0 : Fin (m + 1))]

/--
Chapter 13's least-explored alternative arm.

There are `m + 1` arms: arm zero is the base arm and `i.succ`, for `i : Fin m`,
are the alternatives. The hypotheses are precisely the expected pull-count
nonnegativity and total-budget identity needed by the averaging argument.
-/
theorem exists_leastExploredAlternative
    {m : Nat} (hm : 0 < m)
    (expectedPulls : Fin (m + 1) -> Real)
    (horizon : Nat)
    (hnonneg : ∀ arm, 0 ≤ expectedPulls arm)
    (htotal : ∑ arm : Fin (m + 1), expectedPulls arm = (horizon : Real)) :
    ∃ i : Fin m,
      expectedPulls i.succ ≤ (horizon : Real) / (m : Real) := by
  exact exists_alternative_le_average hm
    (fun i : Fin m => expectedPulls i.succ) (horizon : Real)
    (alternativeExpectedPullBudget_le expectedPulls (horizon : Real) hnonneg htotal)

/-- The exact deterministic expression in the base-environment identity (13.2). -/
def baseEnvironmentRegret
    (horizon : Nat) (gap baseFirstExpectedPulls : Real) : Real :=
  gap * ((horizon : Real) - baseFirstExpectedPulls)

/-- The changed-environment regret lower expression on the right of (13.3). -/
def changedEnvironmentRegretLowerBound
    (gap changedFirstExpectedPulls : Real) : Real :=
  gap * changedFirstExpectedPulls

/--
Quantitative algebraic core of the two-environment heuristic.

The premise bounds the cross-environment discrepancy in the expected number
of base-arm pulls. Chapter 13 writes these expectations as approximately
equal; later information-theoretic chapters must supply an actual value of
`error`. This theorem neither derives that premise nor proves Theorem 13.1.
-/
theorem max_base_changed_regretLowerBound_ge_half_sub_error
    (horizon : Nat)
    (gap baseFirstExpectedPulls changedFirstExpectedPulls error : Real)
    (hgap : 0 ≤ gap)
    (hpullDifference : baseFirstExpectedPulls - changedFirstExpectedPulls ≤ error) :
    gap * ((horizon : Real) - error) / 2 ≤
      max
        (baseEnvironmentRegret horizon gap baseFirstExpectedPulls)
        (changedEnvironmentRegretLowerBound gap changedFirstExpectedPulls) := by
  have hscaled := mul_le_mul_of_nonneg_left hpullDifference hgap
  have hsum :
      gap * ((horizon : Real) - error) ≤
        baseEnvironmentRegret horizon gap baseFirstExpectedPulls +
          changedEnvironmentRegretLowerBound gap changedFirstExpectedPulls := by
    unfold baseEnvironmentRegret changedEnvironmentRegretLowerBound
    nlinarith
  have hbase := le_max_left
    (baseEnvironmentRegret horizon gap baseFirstExpectedPulls)
    (changedEnvironmentRegretLowerBound gap changedFirstExpectedPulls)
  have hchanged := le_max_right
    (baseEnvironmentRegret horizon gap baseFirstExpectedPulls)
    (changedEnvironmentRegretLowerBound gap changedFirstExpectedPulls)
  nlinarith

/--
Zero-error corollary of the quantitative two-environment algebra.

The premise `baseFirstExpectedPulls ≤ changedFirstExpectedPulls` specializes
the pull discrepancy to at most zero. The quantitative predecessor is the
intended interface for later information theorems; neither declaration is the
Gaussian minimax lower bound.
-/
theorem max_base_changed_regretLowerBound_ge_half
    (horizon : Nat) (gap baseFirstExpectedPulls changedFirstExpectedPulls : Real)
    (hgap : 0 ≤ gap)
    (htransport : baseFirstExpectedPulls ≤ changedFirstExpectedPulls) :
    gap * (horizon : Real) / 2 ≤
      max
        (baseEnvironmentRegret horizon gap baseFirstExpectedPulls)
        (changedEnvironmentRegretLowerBound gap changedFirstExpectedPulls) := by
  have h := max_base_changed_regretLowerBound_ge_half_sub_error
    horizon gap baseFirstExpectedPulls changedFirstExpectedPulls 0 hgap
    (sub_nonpos.mpr htransport)
  simpa using h

end LowerBounds
end BanditRLProof
