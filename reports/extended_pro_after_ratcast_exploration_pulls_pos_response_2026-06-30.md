# Extended Pro Response After Rat-Cast ETC Denominator Positivity

- Prompt: `reports/extended_pro_after_ratcast_exploration_pulls_pos_candidate_prompt_2026-06-30.md`
- Boundary: `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS`
- Reviewer: ChatGPT Extended Pro
- Status: response received

## Selected Leaf

Extended Pro selected Candidate A:

`ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO`

It judged this to be the natural corollary of the compiled Rat positivity
adapter and the exact denominator contract future Rat division lemmas will
want.  It said empirical-mean API design and pairwise concentration route
discovery should wait until this denominator contract is pinned.

## Exact Lean-Facing Statement

Extended Pro preferred the ASCII `Not ... = ...` form first:

```lean
theorem ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    Not ((pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat) = 0)
```

## Local APIs / Imports

Local API:

```lean
ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos
```

Likely project import:

```lean
import BanditRLProof.Algorithms.ETCTraceCountLemmas
```

No new probability, measurability, concentration, or cast import should be
needed.  The earlier Rat positivity leaf already handled the Nat-to-Rat cast.

## Intended Proof Route

Invoke the compiled Rat positivity theorem:

```lean
have hpos :
    (0 : Rat) < (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat) :=
  ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos
    spec commitArm a hexplorationPulls_pos
```

Then close by:

```lean
exact ne_of_gt hpos
```

## Regularity Contracts

Keep exactly:

```lean
{K : Nat}
(spec : ETC.Spec K)
(commitArm a : Fin K)
(hexplorationPulls_pos : 0 < spec.explorationPulls)
```

Do not introduce:

- empirical-mean definitions;
- division or zero-fallback choices;
- measures, measurability, probability, filtration, conditional expectation,
  or independence;
- Hoeffding, sub-Gaussian, martingale, or pairwise concentration assumptions;
- final ETC theorem assumptions.

## Retrieval Evidence

Local evidence:

- `ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos` is the
  exact positivity input needed by `ne_of_gt`.

Mathlib evidence:

- Ordered-field/order infrastructure provides `ne_of_gt`, which turns strict
  positivity into nonzeroness.  No LML or concentration theorem is involved.

## Status

Project-local denominator adapter.

This is not a Mathlib candidate, not a port candidate, and not
theorem-card-only.

## Failure Policy

If the direct proof fails:

1. Use a named `hpos`.
2. If `ne_of_gt` orientation is brittle, prove by contradiction and rewrite the
   denominator to zero inside `hpos`.
3. If notation causes parser issues, keep the ASCII conclusion
   `Not ((...) = 0)`.
4. Stop after this theorem compiles.

Do not start empirical means, concentration route discovery, or a final ETC
theorem in this batch.

## Assessment Of Rat-Cast Positivity Adapter

Extended Pro judged the Rat-cast positivity adapter reasonable after the Nat
denominator leaf.  It described the intended order as:

```text
exact deterministic pull count
-> Nat positivity
-> Rat positivity
-> Rat nonzero denominator
```

This prepares future empirical-mean construction without prematurely choosing
the full empirical-mean API.
