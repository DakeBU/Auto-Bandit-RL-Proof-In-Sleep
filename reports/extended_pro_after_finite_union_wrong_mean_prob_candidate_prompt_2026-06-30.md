# Extended Pro Review Prompt: After Finite-Union Wrong-Mean Probability Wrapper

- Date: 2026-06-30
- Local gate before review: `python3 tools\bandit.py check` passed in the previous batch after compiling `ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM`.
- Current boundary:
  `ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM`

## Current Lean-Compiled ETC Layer

In `BanditRLProof/Algorithms/ETCMeasurability.lean`, the following local leaves compile:

```lean
ETC.measurableSet_commitArm_ne_bestArm
ETC.measurableSet_empMean_ge_empMean
ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm
ETC.wrong_commit_subset_exists_empMean_ge_bestArm
ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset
ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum
```

The newest compiled theorem is:

```lean
theorem ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat) :
    mu {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        mu {omega : Omega | (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm})
```

It was proved by rewriting the existential wrong-mean event as a bounded union
over `Finset.univ` and applying:

```lean
MeasureTheory.measure_biUnion_finset_le
```

No event measurability, probability measure, concentration, filtration,
empirical-mean construction, or final regret theorem was introduced.

## Current Ledger Status

`python3 tools\bandit.py unfinished` now records:

```text
ETC-WRONG-COMMIT-PROBABILITY-DESIGN ...
contract: probability measure, measurable `commitArm`, measurable empirical means,
explicit argmax contract; commit-arm wrong-event measurability, pairwise
empirical-mean comparison measurability, finite existential wrong-mean event
measurability, pure set inclusion, measure monotonicity wrapper, and finite-union
probability wrapper now compiled; still missing empirical-mean construction,
pairwise concentration/tails, filtration, and final ETC theorem

BRL-OP-ETC-SUBGAUSS-001 ...
next leaf: `ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM` compiled;
next ask reviewer to choose empirical-mean construction/denominator positivity,
pairwise tail wrapper, or final event assembly
```

## Decision Needed

Please choose exactly one next leaf row. Do not choose a broad theorem such as
"prove ETC regret", "prove Hoeffding", "formalize sub-Gaussian", or
"build filtration". We need one Lean-facing leaf that is small enough to compile
before the next reviewer checkpoint.

Candidate A: final elementary event assembly

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events
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
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        mu {omega : Omega | (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm})
```

This would simply compose
`ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset` with
`ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`. It is still not a
concentration theorem or final regret theorem.

Candidate B: empirical-mean construction / denominator positivity design leaf

Choose a precise local statement that connects the project ETC exploration
counts / reward sums to a well-defined `empMean`, with explicit positivity or
nonzero denominator side conditions. Please keep it deterministic or
measurability-only unless a probability assumption is truly required.

Candidate C: pairwise tail wrapper under an explicit abstract tail assumption

Choose a precise local wrapper that does not prove Hoeffding/sub-Gaussian yet,
but consumes an assumption of the form:

```lean
forall a : Fin K, a != model.bestArm ->
  mu {omega | empMean omega a >= empMean omega model.bestArm} <= tail a
```

and combines it with the finite-union wrong-mean wrapper. If this is chosen,
please give the exact `ENNReal`/measure statement and side conditions.

## Required Output Format

For the chosen leaf, write:

- exact Lean-facing statement;
- local APIs/imports;
- intended proof route;
- regularity contracts;
- retrieval evidence from Mathlib/LML/local declarations;
- status: imported, port candidate, Mathlib candidate, project-local, or theorem-card-only;
- failure policy.

Also explicitly say which candidates should not be started in the same batch.
