# Extended Pro Review Prompt: After ETC Wrong-Commit Probability Design

ABRL Lean 4 status:

- The deterministic fixed-commit ETC layer compiles locally through:
  - `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND`;
  - `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE`.
- `python3 tools/bandit.py check` passed after the theorem, tests, docs, and
  retrieval index were updated.
- Extended Pro selected `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as
  theorem-card-only / missing-leaf design, not a local Lean proof.
- The design card is recorded in
  `research-wiki/open-problems/etc-wrong-commit-probability-design.md`.

Current theorem-card shape:

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_commit : Measurable commitArm)
    (hmeas_empMean : forall a : Fin K, Measurable (fun omega => empMean omega a))
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega))
    (hbest_gap_pos :
      forall a : Fin K, (a = model.bestArm -> False) -> 0 < model.gap a) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    mu {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm}
```

Do not choose a broad final theorem.  Do not start Hoeffding, sub-Gaussian,
martingale, filtration, conditional expectation, or final ETC/UCB theorem work
yet.  Pick exactly one next compiled leaf or a stop/import-route decision.

## Candidate A: Commit-Arm Wrong-Event Measurability

Compile the smallest event canary saying the wrong-commit event is measurable
from a measurable finite-valued commit arm.

Possible Lean-facing statement:

```lean
theorem measurableSet_commitArm_ne_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (hmeas_commit : Measurable commitArm) :
    MeasurableSet {omega : Omega | commitArm omega = model.bestArm -> False}
```

Expected route: rewrite as the complement of the equality event
`{omega | commitArm omega = model.bestArm}`, use `hmeas_commit` and singleton
measurability, then close by measurable-set complement.

## Candidate B: Empirical-Mean Comparison-Event Measurability

Compile the smallest event canary saying a pairwise empirical-mean comparison
event is measurable.

Possible Lean-facing statement:

```lean
theorem measurableSet_empMean_ge_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean : forall a : Fin K, Measurable (fun omega => empMean omega a))
    (a b : Fin K) :
    MeasurableSet {omega : Omega | empMean omega a >= empMean omega b}
```

Expected route: use Mathlib measurable comparison lemmas for ordered codomains,
or identify the exact imports/instances needed for `Rat`.

## Candidate C: Generic Mathlib Import/Wrapper First

Do not write an ETC-specific proof in this batch.  Instead identify the exact
generic Mathlib import or local wrapper that should precede Candidate A/B, such
as a reusable measurable-set wrapper for `f x != c` or for ordered pairwise
comparisons.  If this is the right answer, give the exact wrapper statement.

Requested response:

1. Pick exactly one next leaf or stop/import-route decision.
2. Give the exact Lean-facing statement if it is a local proof leaf.
3. List local APIs/imports.
4. Give the intended proof route or design route.
5. State regularity contracts.
6. Give retrieval evidence from Mathlib/LML/local declarations.
7. Classify it as imported, port candidate, Mathlib candidate, project-local,
   theorem-card-only, or missing-leaf.
8. Give a failure policy.
