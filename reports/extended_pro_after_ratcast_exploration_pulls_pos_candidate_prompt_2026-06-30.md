# Extended Pro Candidate Prompt After Rat-Cast ETC Denominator Positivity

We are continuing the ABRL Lean 4 project.

Please review the current boundary and select exactly one next unfinished leaf.
Do not recommend a broad theorem such as full ETC regret, Hoeffding,
sub-Gaussian concentration, filtration, conditional expectation, UCB, TS,
EXP3, Tsallis-INF, OFUL, RL, or a final theorem.

## Current Compiled Boundary

The previous reviewer-selected leaf was:

```lean
theorem ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    (0 : Rat) < (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat)
```

It compiles locally in `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
`lake build BanditRLProof.Algorithms.ETCTraceCountLemmas` and
`lake build Tests` passed after this theorem and its canary were added.

The proof consumes:

```lean
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos
```

and transports the Nat positivity theorem across the Nat-to-Rat cast.

## Current Local APIs

- `pullCount : ActionTrace Action -> Action -> Nat -> Nat`
- `sumRewards : ActionTrace Action -> RewardTrace Reward -> Action -> Nat -> Reward`
- `ETC.actionWithCommit : ETC.Spec K -> Fin K -> Nat -> Fin K`
- `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`
- `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos`
- `ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos`
- Rat-valued reward/regret infrastructure exists locally, but there is still
  no compiled concrete ETC empirical-mean definition.

## Candidate A: Rat-cast nonzero denominator corollary

Leaf id:

`ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO`

Exact Lean-facing statement:

```lean
theorem ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    Not ((pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat) = 0)
```

If the repository prefers Unicode notation, the conclusion can be written as:

```lean
(pullCount (ETC.actionWithCommit spec commitArm) a
  (spec.explorationPulls * K) : Rat) != 0
```

or with Lean's `not equal` notation.

Local APIs/imports:

- `BanditRLProof.Algorithms.ETCTraceCountLemmas`
- `ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos`
- `ne_of_gt`

Intended proof route:

Use the compiled Rat positivity theorem, then close with `ne_of_gt`.

Regularity contracts:

- `{K : Nat}`
- `spec : ETC.Spec K`
- `commitArm a : Fin K`
- `hexplorationPulls_pos : 0 < spec.explorationPulls`
- no measure, probability, empirical mean definition, concentration,
  filtration, conditional expectation, independence, or final ETC theorem

Status if selected:

project-local denominator adapter.

Failure policy:

If notation is brittle, keep the ASCII `Not ((...) = 0)` statement.  Do not
start empirical means in the same batch.

## Candidate B: Start concrete ETC empirical-mean definition

Possible direction:

Define an empirical mean from `sumRewards` divided by the pull count at
`spec.explorationPulls * K`.

Concern:

This may still force API choices about:

- whether the denominator is `Nat`, `Rat`, or a subtype;
- whether the definition includes a zero fallback;
- whether the reward trace is deterministic or random-variable-facing;
- where measurability should enter.

## Candidate C: Actual pairwise concentration route discovery

Possible direction:

Create an import-route/theorem-card for the exact Mathlib/LML theorem shape
needed for:

```lean
mu {omega : Omega |
  empMean omega a >= empMean omega model.bestArm} <= tail a
```

Concern:

This likely requires a stable empirical-mean object and sampling model first.

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

Also state whether the compiled Rat-cast positivity adapter was a reasonable
step after the Nat denominator leaf.
