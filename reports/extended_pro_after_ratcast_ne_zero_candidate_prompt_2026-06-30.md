# Extended Pro Candidate Prompt After Rat Nonzero ETC Denominator Adapter

We are continuing the ABRL Lean 4 project.

Please review the current boundary and select exactly one next unfinished leaf.
Do not recommend a broad theorem such as full ETC regret, Hoeffding,
sub-Gaussian concentration, filtration, conditional expectation, UCB, TS,
EXP3, Tsallis-INF, OFUL, RL, or a final theorem.

## Current Compiled Boundary

The previous reviewer-selected leaf was:

```lean
theorem ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    Not ((pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat) = 0)
```

It compiles locally in `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
`python3 tools/bandit.py check` passed after this theorem and its test canary.

The denominator chain now has:

```lean
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos
ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos
ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero
```

## Current Local APIs

- `pullCount : ActionTrace Action -> Action -> Nat -> Nat`
- `sumRewards : ActionTrace Action -> RewardTrace Reward -> Action -> Nat -> Reward`
- `ETC.actionWithCommit : ETC.Spec K -> Fin K -> Nat -> Fin K`
- Rat-valued reward/regret infrastructure exists locally.
- There is still no compiled concrete ETC empirical-mean definition.
- Existing wrong-commit probability wrappers consume an abstract
  `empMean : Omega -> Fin K -> Rat`; they do not yet connect that `empMean` to
  `sumRewards` and `pullCount`.

## Candidate A: Deterministic ETC empirical-mean definition at exploration horizon

Leaf id:

`ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION`

Exact Lean-facing definition:

```lean
def ETC.empMeanAtExploration
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) : Rat :=
  sumRewards (ETC.actionWithCommit spec commitArm) reward a
      (spec.explorationPulls * K) /
    (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat)
```

Exact companion theorem:

```lean
theorem ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) :
    ETC.empMeanAtExploration spec commitArm reward a =
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
          (spec.explorationPulls * K) /
        ((spec.explorationPulls : Nat) : Rat)
```

Local APIs/imports:

- likely `BanditRLProof.Algorithms.ETCTraceCountLemmas`
- `sumRewards`
- `ETC.actionWithCommit`
- `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`

Intended proof route:

Define the total Rat expression, then prove the denominator rewrite by
unfolding and simplifying with the exact pull-count theorem.  A local smoke
test with the existing import chain passed.

Regularity contracts:

- `{K : Nat}`
- `spec : ETC.Spec K`
- `commitArm a : Fin K`
- `reward : RewardTrace Rat`
- no measure, probability, measurability, stochastic reward model,
  concentration, filtration, conditional expectation, independence, commit
  argmax, or final ETC theorem

Concern:

Rat division is total, so the definition itself does not enforce the nonzero
denominator.  The previously compiled nonzero theorem supplies the separate
contract for future algebraic division lemmas.  This leaf intentionally avoids
choosing a random-variable-facing empirical mean.

## Candidate B: Empirical-mean nonzero-denominator theorem for the new definition

Only select this if Candidate A is too broad or should be split differently.
Possible leaf shape:

```lean
theorem ETC.empMeanAtExploration_denominator_ne_zero
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    Not ((pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat) = 0)
```

Concern:

This is almost identical to the compiled denominator theorem and may not move
the empirical-mean API forward unless it is attached to a new definition or a
specific simplification lemma.

## Candidate C: Actual pairwise concentration route discovery

Possible direction:

Create an import-route/theorem-card for the exact Mathlib/LML theorem shape
needed for:

```lean
mu {omega : Omega |
  empMean omega a >= empMean omega model.bestArm} <= tail a
```

Concern:

This likely still requires a stable empirical-mean object and sampling model
first.  It should remain theorem-card-only if selected.

## Question

Which one exact next leaf should we implement now?

Please answer with:

1. Selected candidate or a replacement exact leaf id.
2. Exact Lean-facing statement or definition plus theorem, if the selected
   leaf necessarily includes both.
3. Local APIs/imports.
4. Intended proof route.
5. Regularity contracts.
6. Retrieval evidence from Mathlib/local declarations.
7. Status: imported, port candidate, Mathlib candidate, project-local, or
   theorem-card-only.
8. Failure policy.

Also state whether the compiled Rat nonzero denominator adapter was a
reasonable step before empirical-mean construction.
