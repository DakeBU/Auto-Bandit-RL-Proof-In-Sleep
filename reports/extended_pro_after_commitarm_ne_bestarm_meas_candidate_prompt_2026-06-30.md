# Extended Pro Review Prompt: After ETC CommitArm Wrong-Event Measurability

ABRL Lean 4 status:

- The deterministic fixed-commit ETC layer compiles locally through:
  - `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND`;
  - `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE`.
- Extended Pro selected `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as a
  theorem-card-only / missing-leaf design.
- Extended Pro then selected Candidate A at the next boundary:
  `ETC.measurableSet_commitArm_ne_bestArm`.
- That theorem now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- `python3 tools/bandit.py check` passed after code, tests, docs, and the
  retrieval index were updated.

Newest compiled theorem:

```lean
theorem ETC.measurableSet_commitArm_ne_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (hmeas_commit : Measurable commitArm) :
    MeasurableSet {omega : Omega | commitArm omega = model.bestArm -> False}
```

Current theorem-card target remains:

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

## Candidate A: Pairwise Empirical-Mean Comparison Event

Compile the smallest pairwise comparison measurability canary.

Possible Lean-facing statement:

```lean
theorem ETC.measurableSet_empMean_ge_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean : forall a : Fin K, Measurable (fun omega => empMean omega a))
    (a b : Fin K) :
    MeasurableSet {omega : Omega | empMean omega a >= empMean omega b}
```

Expected route: identify the exact Mathlib imports/instances for measurable
ordered comparisons into `Rat`, then use the measurability of both coordinate
maps.

## Candidate B: Finite Existential Wrong-Mean Event Measurability

Compile the finite-exists event measurability wrapper after pairwise
comparison measurability is available or by proving pairwise comparison inline.

Possible Lean-facing statement:

```lean
theorem ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean : forall a : Fin K, Measurable (fun omega => empMean omega a)) :
    MeasurableSet {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm}
```

Expected route: finite union over `Fin K` of measurable pairwise comparison
events intersected with the proposition `a = model.bestArm -> False`.

## Candidate C: Pure Wrong-Commit Set Inclusion

Compile the core event reduction as a pure set inclusion with no measure and no
measurability assumptions.

Possible Lean-facing statement:

```lean
theorem ETC.wrong_commit_subset_exists_empMean_ge_bestArm
    {Omega : Type u} {K : Nat}
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega)) :
    Set.Subset
      {omega : Omega | commitArm omega = model.bestArm -> False}
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}
```

Expected route: for `omega` in the wrong-commit event, choose
`a := commitArm omega`; use `hcommit_argmax omega model.bestArm`.

## Candidate D: Stop And Refine Imports

Do not write a local proof in this batch.  Instead identify the exact Mathlib
ordered-measurability imports or local wrappers needed before Candidate A/B/C.

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
