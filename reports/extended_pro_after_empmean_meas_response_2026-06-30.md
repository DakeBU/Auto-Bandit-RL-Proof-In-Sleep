## 1. Selected leaf

**Candidate B: empirical-mean coordinate bundle/wrapper.**

Leaf id:

```text
ETC-MEASURABLE-EMPMEAN-AT-EXPLORATION-COORDINATES
```

This is the best next leaf. It is a thin wrapper around the already compiled coordinate theorem, but it produces exactly the `hmeas_empMean` shape consumed by existing event-measurability lemmas such as:

```lean
ETC.measurableSet_empMean_ge_empMean
ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm
```

Candidate A is tempting, but the commit-oracle layer risks a circular design because `ETC.empMeanAtExploration spec commitArm ...` currently takes a fixed `commitArm`. Before introducing oracle selection, first package the concrete empirical mean in the same `Omega -> Fin K -> Rat` shape used by the probability layer.

---

## 2. Exact Lean-facing statement

Recommended statement:

```lean
theorem ETC.measurable_empMeanAtExploration_coordinates
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    forall a : Fin K,
      Measurable (fun omega : Omega =>
        (fun b : Fin K =>
          ETC.empMeanAtExploration spec commitArm (reward omega) b) a) := by
  intro a
  simpa using
    (ETC.measurable_empMeanAtExploration
      spec commitArm a reward hreward)
```

A slightly cleaner equivalent statement is:

```lean
theorem ETC.measurable_empMeanAtExploration_coordinate
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    forall a : Fin K,
      Measurable (fun omega : Omega =>
        ETC.empMeanAtExploration spec commitArm (reward omega) a) := by
  intro a
  exact ETC.measurable_empMeanAtExploration
    spec commitArm a reward hreward
```

I prefer the first version because it syntactically exposes the bundled empirical-mean function:

```lean
fun omega : Omega =>
  fun b : Fin K =>
    ETC.empMeanAtExploration spec commitArm (reward omega) b
```

That is the exact shape to pass later as the abstract `empMean`.

---

## 3. Local APIs / imports

Required local API:

```lean
ETC.empMeanAtExploration
ETC.measurable_empMeanAtExploration
```

Likely import:

```lean
import BanditRLProof.Algorithms.ETCTraceCountLemmas
```

or whichever local file currently exports:

```lean
ETC.empMeanAtExploration
ETC.measurable_empMeanAtExploration
```

No new Mathlib import should be needed. The proof uses only `intro`, `exact`/`simpa`, and the already compiled theorem.

---

## 4. Intended proof route

The proof is immediate.

1. Introduce the coordinate:

```lean
intro a
```

2. Apply the compiled theorem:

```lean
ETC.measurable_empMeanAtExploration
  spec commitArm a reward hreward
```

3. If using the bundled-function statement, close with `simpa` because:

```lean
(fun b => ETC.empMeanAtExploration spec commitArm (reward omega) b) a
```

reduces to:

```lean
ETC.empMeanAtExploration spec commitArm (reward omega) a
```

Proof skeleton:

```lean
by
  intro a
  simpa using
    (ETC.measurable_empMeanAtExploration
      spec commitArm a reward hreward)
```

---

## 5. Regularity contracts

Keep exactly the same contracts as the compiled full empirical-mean measurability theorem:

```lean
[MeasurableSpace Omega]
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
[MeasurableSpace Rat]
[MeasurableSingletonClass Rat]
[MeasurableAdd₂ Rat]
```

and:

```lean
hreward : forall t : Nat,
  Measurable (fun omega : Omega => reward omega t)
```

Do **not** add:

```lean
mu : Measure Omega
[IsProbabilityMeasure mu]
commitArm : Omega -> Fin K
ETC.CommitOracle K
hcommit_argmax
hchoose_argmax
hpair_tail
filtration
conditional expectation
independence
sub-Gaussianity
concentration
```

Also do not require denominator nonzero or `hexplorationPulls_pos`; measurability of total `Rat` division already compiled without it.

---

## 6. Retrieval evidence

Local evidence is decisive:

```lean
ETC.measurable_empMeanAtExploration
```

already proves every coordinate:

```lean
Measurable (fun omega =>
  ETC.empMeanAtExploration spec commitArm (reward omega) a)
```

for any fixed `a`.

The existing probability/event layer expects exactly this kind of coordinate contract:

```lean
hmeas_empMean :
  forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)
```

for an abstract empirical-mean function:

```lean
empMean : Omega -> Fin K -> Rat
```

This wrapper bridges the concrete empirical mean into that abstract shape.

No LML, Hoeffding, sub-Gaussian, martingale, or conditional-expectation retrieval is relevant for this leaf.

---

## 7. Status

**Status:** project-local.

This is not imported, not a port candidate, not a Mathlib candidate, and not theorem-card-only. It is a local adapter from the concrete ETC empirical-mean API to the existing abstract measurability interface.

---

## 8. Failure policy

Implement exactly this wrapper and stop.

If it fails:

1. Use the simpler coordinate statement first:

```lean
forall a : Fin K,
  Measurable (fun omega : Omega =>
    ETC.empMeanAtExploration spec commitArm (reward omega) a)
```

2. If namespace qualification fails, switch between qualified and unqualified names depending on whether the theorem is inside `namespace ETC`.

3. If `simpa` fails in the bundled-function version, use the simpler statement or write:

```lean
change Measurable (fun omega : Omega =>
  ETC.empMeanAtExploration spec commitArm (reward omega) a)
exact ETC.measurable_empMeanAtExploration
  spec commitArm a reward hreward
```

4. Do not introduce `ETC.CommitOracle`, argmax contracts, pairwise concentration, filtration, conditional expectation, or final probability instantiation in this batch.

After this compiles, the next plausible leaf is a **deterministic commit-oracle argmax consumer** that stays abstract and avoids proving oracle optimality or measurability.
