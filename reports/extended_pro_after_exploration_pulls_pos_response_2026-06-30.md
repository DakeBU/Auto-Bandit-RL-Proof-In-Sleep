# Extended Pro Response After ETC Exploration Pull-Count Positivity

- Prompt: `reports/extended_pro_after_exploration_pulls_pos_candidate_prompt_2026-06-30.md`
- Boundary: `ETC-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS`
- Reviewer: ChatGPT Extended Pro
- Status: response received

## Selected Leaf

Extended Pro selected Candidate A:

`ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS`

It judged this to be the correct next leaf because it is a minimal adapter from
the compiled Nat positivity fact to the rational denominator layer needed for
future Rat empirical means.  It explicitly said Candidate B, the nonzero
corollary, should follow later from Candidate A, and Candidate C, the concrete
empirical-mean definition, is still too broad.

## Exact Lean-Facing Statement

```lean
theorem ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    (0 : Rat) < (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat)
```

## Local APIs / Imports

Local API:

```lean
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos
```

Likely imports:

```lean
import BanditRLProof.Algorithms.ETCTraceCountLemmas
import Mathlib.Data.Rat.Cast.Order
```

Extended Pro suggested trying the existing import chain first.  If
`exact_mod_cast` is unavailable, add `Mathlib.Tactic`; otherwise use the
narrower cast-order theorem route.

## Intended Proof Route

First obtain the compiled Nat positivity theorem:

```lean
have hnat :
    0 < pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) :=
  ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos
    spec commitArm a hexplorationPulls_pos
```

Then transport it across the Nat-to-Rat cast:

```lean
exact_mod_cast hnat
```

If tactic import is undesirable, use `Nat.cast_pos'` or `Nat.cast_lt` directly.

## Regularity Contracts

Keep exactly the deterministic assumptions of the Nat leaf:

```lean
{K : Nat}
(spec : ETC.Spec K)
(commitArm a : Fin K)
(hexplorationPulls_pos : 0 < spec.explorationPulls)
```

Do not add:

- measurable spaces;
- measures or probability-measure instances;
- `ENNReal`/`Real` tail bounds;
- empirical-mean definitions;
- concentration, filtration, conditional expectation, or independence
  assumptions;
- final ETC theorem assumptions.

## Retrieval Evidence

Local evidence:

- `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos` already compiles
  with exactly the same arguments and target count.

Mathlib evidence:

- `Mathlib.Data.Nat.Cast.Order.Basic` exposes Nat cast-order lemmas such as
  `Nat.cast_pos'` and `Nat.cast_lt`, which are enough to transport
  `0 < n` to `(0 : Rat) < (n : Rat)`.

## Status

Project-local denominator adapter.

This is not a Mathlib candidate.  It ties a project-specific ETC pull-count
theorem to the project's Rat reward/empirical-mean layer.

## Failure Policy

If direct `exact_mod_cast` fails, repair only the cast transport:

1. Use a named `hnat`.
2. If needed, add `Mathlib.Tactic`.
3. If tactic import is undesirable, use `Nat.cast_pos'` or `Nat.cast_lt`.
4. If Rat imports are missing, add `Mathlib.Data.Rat.Cast.Order`.
5. Stop after Candidate A compiles.

Do not add the nonzero corollary or empirical-mean definition in this batch.

## Assessment Of Completed Nat Leaf

Extended Pro judged the completed Nat-level positivity leaf reasonable after
the filtered-sum tail consumer.  It said the current chain keeps a clean
deterministic/probabilistic separation:

```text
wrong-commit event bound
-> pairwise-tail finite sum
-> filtered nonbest sum
-> deterministic exploration denominator support
```

The Rat cast leaf continues that separation and prepares the denominator side
for future empirical means without forcing the empirical-mean definition,
zero-denominator fallback, or concentration assumptions prematurely.
