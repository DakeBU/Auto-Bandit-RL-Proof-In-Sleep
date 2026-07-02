# Extended Pro Review Response: After Coarse ETC Suffix Regret Bound

- Date: 2026-06-30
- Tool/model: ChatGPT Extended Pro
- URL: https://chatgpt.com/c/6a41e1dc-fcf0-83e8-bcb2-27cfa0eab3ad
- Prompt file: `reports/extended_pro_after_coarse_suffix_regret_candidate_prompt_2026-06-30.md`
- Local gate before review: `python3 tools\bandit.py check`
- Boundary:
  `ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND`
- Recorded from raw response:
  `reports/extended_pro_after_coarse_suffix_regret_raw_response_2026-06-30.txt`

## Reviewer Decision

- Chosen next leaf: ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET
- Classification: project-local deterministic ETC regret recurrence/scaffold
- Status: reviewer-approved

## Exact Lean-Facing Statement

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) =
      pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K) +
        (((r : Nat) : Rat) * model.gap commitArm)
```

## Imports And Local APIs

- `import BanditRLProof.RegretCountBounds`
- `import BanditRLProof.Algorithms.ETCTraceCountLemmas`
- `pseudoRegret_succ`
- `ETC.actionWithCommit_eq_commitArm_of_ge`

## Intended Proof Route

1. Induct on the suffix length `r`.
2. In the successor case, use
   `ETC.actionWithCommit_eq_commitArm_of_ge` at
   `t := spec.explorationPulls * K + r`.
3. Rewrite with `pseudoRegret_succ`, the induction hypothesis, and
   `Nat.cast_succ`/`add_mul`.

## Regularity Contracts

- Only `{K : Nat}`, `spec : ETC.Spec K`, `model : FiniteBanditModel K`,
  `commitArm : Fin K`, and `r : Nat`.
- No empirical means, commit argmax, probability, concentration, filtration,
  conditional expectation, or final ETC theorem facts.

## Retrieval Evidence

- Local declarations consumed:
  `pseudoRegret_succ` and `ETC.actionWithCommit_eq_commitArm_of_ge`.
- Classification: project-local compiled ETC deterministic regret scaffold.

## Failure Policy

- Fail closed: do not prove the generic Candidate A or RHS-simplification
  Candidate C in the same batch. Add only a small local arithmetic helper if
  the successor arithmetic becomes brittle.

## Raw Extended Pro Response

Pick

Pick Candidate B: ETC Phase-Splitting Regret Equality.

This is now the right next leaf. You already have coarse and count-budget regret bounds; the missing deterministic ETC fact is the exact phase split:

lean
regret through exploration + r committed pulls
=
exploration regret + r * gap(commitArm)

Candidate A is more reusable but broader. Candidate C is algebraic RHS simplification, but Candidate B gives a more structurally useful theorem without Finset manipulation.

Leaf
ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET
Exact Lean-facing statement

Add to:

BanditRLProof/Algorithms/ETCRegretLemmas.lean
lean
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
      rw [pseudoRegret_succ]
      rw [hact]
      rw [ih]

      have hrat :
          (((Nat.succ r : Nat) : Rat) * model.gap commitArm)
            =
          (((r : Nat) : Rat) * model.gap commitArm + model.gap commitArm) := by
        simp [Nat.cast_succ, add_mul]

      rw [hrat]
      simp [add_assoc]

If the last arithmetic step is brittle, replace the final two lines with:

lean
      rw [hrat]
      ring_nf

but only if ring_nf is already available or you are willing to add a tactic import. Prefer the non-tactic route first.

Imports and local APIs

ETCRegretLemmas.lean should already import most of this. Ensure it has:

lean
import BanditRLProof.LeafLemmas
import BanditRLProof.Algorithms.ETCTrace

If the file currently imports ETCTraceCountLemmas, that likely already brings in the trace APIs. Still, this theorem directly uses:

lean
pseudoRegret_succ
ETC.actionWithCommit_eq_commitArm_of_ge

Local APIs to use:

lean
pseudoRegret_succ
ETC.actionWithCommit_eq_commitArm_of_ge

Do not use or unfold:

lean
pullCount
RegretCountBounds
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
FiniteBanditModel.gap_nonneg

This proof should be by pseudo-regret recurrence, not by count decomposition.

Intended proof route

Induct on r.

Base case: reduce to t + 0 = t and 0 * gap = 0.

Successor case:

rewrite:

lean
spec.explorationPulls * K + Nat.succ r

via:

lean
Nat.add_succ

apply:

lean
pseudoRegret_succ

use:

lean
ETC.actionWithCommit_eq_commitArm_of_ge

at time spec.explorationPulls * K + r;

rewrite with the induction hypothesis;

normalize:

lean
((Nat.succ r : Nat) : Rat) * gap
  =
((r : Nat) : Rat) * gap + gap
Regularity contracts

Require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(model : FiniteBanditModel K)
(commitArm : Fin K)
(r : Nat)

Do not add:

lean
Measure
MeasurableSpace
IsProbabilityMeasure
ENNReal
Real
Integrable
Filtration
SubGaussian
Empirical mean assumptions
Commit correctness assumptions
Concentration assumptions

No separate 0 < K assumption is needed; it is already inside spec : ETC.Spec K.

Retrieval evidence and classification

Local declarations consumed:

lean
pseudoRegret_succ
ETC.actionWithCommit_eq_commitArm_of_ge

Supporting local surface already compiled:

lean
ETC.actionWithCommit
FiniteBanditModel
pseudoRegret

Classification:

ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET:
  project-local compiled ETC deterministic regret recurrence/scaffold

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
empirical-mean leaf
final ETC theorem
Failure policy

If this leaf fails:

First isolate the arithmetic lemma:

lean
have hrat :
    (((Nat.succ r : Nat) : Rat) * model.gap commitArm)
      =
    (((r : Nat) : Rat) * model.gap commitArm + model.gap commitArm) := by
  simp [Nat.cast_succ, add_mul]

If the successor horizon does not match pseudoRegret_succ, use:

lean
change
  pseudoRegret model (ETC.actionWithCommit spec commitArm)
    (Nat.succ (spec.explorationPulls * K + r)) =
  _

after rw [Nat.add_succ].

If ETC.actionWithCommit_eq_commitArm_of_ge does not elaborate, explicitly pass:

lean
(t := spec.explorationPulls * K + r)

If final addition associativity is brittle, use a calc block or, as a last resort, add a local arithmetic helper theorem. Do not import broad tactic machinery unless necessary.

Do not prove Candidate A or Candidate C in the same batch.

Do not introduce empirical means, commit argmax, probability, concentration, filtration, conditional expectation, or final ETC theorem facts.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.
