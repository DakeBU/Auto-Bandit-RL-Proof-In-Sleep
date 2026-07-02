# Extended Pro Candidate Prompt After ETC Exploration Pull-Count Positivity

We are continuing the ABRL Lean 4 project.

Please review the current boundary and select exactly one next unfinished leaf.
Do not recommend a broad theorem such as full ETC regret, Hoeffding,
sub-Gaussian concentration, filtration, conditional expectation, UCB, or RL.

## Current Compiled Boundary

After the filtered-sum pairwise-tail consumer, the last reviewer-selected leaf
was the deterministic Nat-level denominator-positivity support theorem:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    0 < pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K)
```

It compiles locally in `BanditRLProof.Algorithms.ETCTraceCountLemmas`.

The proof consumes:

```lean
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
```

and rewrites the configured exploration-horizon pull count to
`spec.explorationPulls`.

## Current Local APIs

- `pullCount : ActionTrace Action -> Action -> Nat -> Nat`
- `sumRewards : ActionTrace Action -> RewardTrace Reward -> Action -> Nat -> Reward`
- `ETC.actionWithCommit : ETC.Spec K -> Fin K -> Nat -> Fin K`
- `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`
- `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos`
- Rat-valued reward/regret infrastructure already exists locally, but no
  compiled concrete empirical-mean definition for ETC has been introduced.

## Candidate A: Rat-cast positive denominator leaf

Leaf id:

`ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS`

Exact Lean-facing statement:

```lean
theorem ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    (0 : Rat) < (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat)
```

Local APIs/imports:

- `BanditRLProof.Algorithms.ETCTraceCountLemmas`
- likely `Mathlib.Data.Rat.Cast.Order`
- `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos`

Intended proof route:

Use `exact_mod_cast` or a Nat-to-Rat positivity cast theorem to transport
the compiled Nat positivity theorem.

Regularity contracts:

- `{K : Nat}`
- `spec : ETC.Spec K`
- `commitArm a : Fin K`
- `hexplorationPulls_pos : 0 < spec.explorationPulls`
- no measure, probability, empirical mean definition, concentration,
  filtration, conditional expectation, or final ETC theorem

Status if selected:

project-local denominator adapter.

Failure policy:

If `exact_mod_cast` is brittle, use the exact Mathlib Nat-to-Rat cast
positivity theorem.  Do not move to empirical means in the same batch.

## Candidate B: Rat-cast nonzero denominator corollary

Leaf id:

`ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO`

Exact Lean-facing statement:

```lean
theorem ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat) != 0
```

If Lean notation prefers Unicode, the final line can be written with `≠`.

Local APIs/imports:

- Candidate A if already compiled, or direct use of the Nat positivity theorem
- `ne_of_gt`

Intended proof route:

Derive Rat positivity, then close with `ne_of_gt`.

Regularity contracts:

Same as Candidate A.

Status if selected:

project-local denominator adapter.

Failure policy:

If nonzero notation or simp is brittle, first compile Candidate A and defer this
leaf.

## Candidate C: Start concrete ETC empirical-mean definition

Possible direction:

Define an empirical mean from `sumRewards` divided by the pull count at
`spec.explorationPulls * K`.

Concern:

This probably opens API choices about division target type, zero-denominator
fallbacks, reward trace type, and whether the empirical mean is deterministic
or random-variable-facing.  It may be too broad for the next leaf unless the
Rat denominator adapter layer is already sufficient.

## Question

Which one exact next leaf should we implement now?

Please answer with:

1. Selected candidate or a replacement exact leaf id.
2. Exact Lean-facing statement.
3. Local APIs/imports.
4. Intended proof route.
5. Regularity contracts.
6. Retrieval evidence from Mathlib/local declarations.
7. Status: imported, port candidate, Mathlib candidate, project-local, or
   theorem-card-only.
8. Failure policy.

Also state whether the completed Nat-level pull-count positivity leaf was a
reasonable step after the filtered-sum tail consumer.
