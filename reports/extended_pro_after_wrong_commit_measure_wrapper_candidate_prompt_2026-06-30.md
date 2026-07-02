# Extended Pro Review Prompt: After ETC Wrong-Commit Measure Wrapper

ABRL Lean 4 status:

- The deterministic fixed-commit ETC layer compiles locally through best-arm
  commit/suffix regret facts.
- Extended Pro selected `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as a
  theorem-card-only / missing-leaf design.
- The following wrong-commit subleaves now compile locally in
  `BanditRLProof.Algorithms.ETCMeasurability`:

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

`python3 tools/bandit.py check` passed after the measure wrapper.

Current theorem-card target remains the full wrong-commit probability bridge,
but the pure set inclusion and arbitrary-measure monotonicity wrapper are now
compiled.  The open local gap is event structure/regularity for the wrong-mean
RHS before any concentration route.

Do not choose a broad final theorem.  Do not start Hoeffding, sub-Gaussian,
martingale, filtration, conditional expectation, UCB, Thompson sampling, EXP3,
Tsallis-INF, OFUL, RL, or final theorem work yet.  Pick exactly one next
compiled leaf or a stop/import-route decision.

Local Mathlib retrieval evidence:

- `measurableSet_le` appears in
  `Mathlib.MeasureTheory.Constructions.BorelSpace.Order`.
- `Rat.instMeasurableSpace` and `Rat.instMeasurableSingletonClass` appear in
  `Mathlib.MeasureTheory.MeasurableSpace.Instances`.
- The local file already imports
  `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`,
  `Mathlib.MeasureTheory.MeasurableSpace.Basic`, and `BanditRLProof.Core`.

## Candidate A: Pairwise Empirical-Mean Comparison Event Measurability

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

Expected route: import or expose ordered Borel-space API, then use
`measurableSet_le` on `hmeas_empMean b` and `hmeas_empMean a`, possibly with a
`change`/`simpa [ge_iff_le]`.

## Candidate B: Finite Existential Wrong-Mean Event Measurability

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
events intersected with or gated by the proposition
`a = model.bestArm -> False`.

## Candidate C: Stop / Import-Route First

If both A and B are premature, explain the exact missing Mathlib import,
local wrapper, or statement correction needed before any proof attempt.

## Required Answer Format

1. Pick exactly one of A/B/C.
2. Give the exact Lean-facing statement to attempt.
3. List local APIs/imports.
4. Give the proof route.
5. State regularity contracts and assumptions to avoid.
6. Give retrieval evidence from Mathlib/LML/local declarations.
7. Classify status as imported, port candidate, Mathlib candidate,
   project-local, or theorem-card-only.
8. Failure policy: what to record if it does not compile after a focused
   attempt, and what not to pivot into.
