# Extended Pro Review Prompt: After ETC Wrong-Commit Set Inclusion

ABRL Lean 4 status:

- The deterministic fixed-commit ETC layer compiles locally through:
  - `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND`;
  - `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE`.
- Extended Pro selected `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as a
  theorem-card-only / missing-leaf design.
- Extended Pro then selected and approved two local subleaves:
  - `ETC.measurableSet_commitArm_ne_bestArm`;
  - `ETC.wrong_commit_subset_exists_empMean_ge_bestArm`.
- Both now compile locally in `BanditRLProof.Algorithms.ETCMeasurability`.
- `python3 tools/bandit.py check` passed after code, tests, docs, and the
  retrieval index were updated.

Newest compiled theorem:

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

Already compiled wrong-commit event measurability canary:

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
martingale, filtration, conditional expectation, UCB, Thompson sampling, EXP3,
Tsallis-INF, OFUL, or RL theorem work yet.  Pick exactly one next compiled leaf
or a stop/import-route decision.

## Candidate A: Measure/Probability Wrapper For The Compiled Set Inclusion

Compile the smallest probability-facing wrapper that uses the already compiled
set inclusion and Mathlib measure monotonicity.

Possible Lean-facing statement:

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega)) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    mu {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm}
```

Expected route: apply `MeasureTheory.Measure.mono` or the local Mathlib name
for measure monotonicity to
`ETC.wrong_commit_subset_exists_empMean_ge_bestArm model commitArm empMean hcommit_argmax`.

Important question: does this need `[MeasurableSpace Omega]`, probability
instance, or measurability of either event?  If not, say which assumptions should
be removed.

## Candidate B: Pairwise Empirical-Mean Comparison Event Measurability

Compile the smallest ordered-measurability canary for empirical means.

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

## Candidate C: Finite Existential Wrong-Mean Event Measurability

Compile the finite-exists event measurability wrapper after pairwise comparison
measurability is available or by proving pairwise comparison inline.

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

## Candidate D: Stop / Import-Route First

If all three candidates are premature, explain the exact missing Mathlib import,
local wrapper, or statement correction needed before any proof attempt.

## Required Answer Format

1. Pick exactly one of A/B/C/D.
2. Give the exact Lean-facing statement to attempt.
3. List local APIs/imports.
4. Give the proof route.
5. State regularity contracts and assumptions to avoid.
6. Give retrieval evidence from Mathlib/LML/local declarations.
7. Classify status as imported, port candidate, Mathlib candidate,
   project-local, or theorem-card-only.
8. Failure policy: what to record if it does not compile after a focused
   attempt, and what not to pivot into.
