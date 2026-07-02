## Review of completed leaf

`ETC.measurable_empMeanVector_of_forall_measurable` is reasonable and well-scoped.

It is exactly the missing coordinate-to-vector bridge:

```lean
Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))
```

from coordinate hypotheses

```lean
forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)
```

The proof

```lean
by
  exact measurable_pi_lambda _ hmeas_coord
```

is the canonical Mathlib route. It does not introduce probability, oracle correctness, finite argmax, concentration, or event logic. It also correctly avoids unnecessary assumptions such as `[MeasurableSpace (Fin K)]`, `[Countable (Fin K -> Rat)]`, or `[MeasurableSingletonClass (Fin K -> Rat)]`.

One important typeclass caution: this theorem proves measurability into the **Pi measurable space** on `Fin K -> Rat`, induced by `[MeasurableSpace Rat]`. Downstream wrappers should avoid adding an arbitrary local

```lean
[MeasurableSpace (Fin K -> Rat)]
```

unless the existing local theorem already requires it, because that can create instance mismatch.

---

## Selected next leaf: Candidate A

Choose:

```text
ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES
```

This is the right next leaf because it is a direct one-step composition of:

1. the new coordinate-to-vector bridge;
2. the existing oracle-choice measurability bridge.

It remains project-local, small, and purely measurable-space level.

---

## Exact Lean-facing statement

The candidate statement is essentially correct. I would use this exact version:

```lean
theorem ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    [MeasurableSpace (Fin K)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => oracle.choose (empMean omega))
```

Do **not** add:

```lean
[MeasurableSpace (Fin K -> Rat)]
```

unless `#check ETC.measurable_commitOracle_choose_of_measurable_empMeanVector` shows that the existing bridge already has it. The safer route is to keep `[MeasurableSpace Rat]` so that the Pi measurable-space instance is synthesized consistently.

If the existing oracle-choice bridge unexpectedly requires output singletons, then the corrected strengthened version is:

```lean
theorem ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    [MeasurableSpace (Fin K)]
    [MeasurableSingletonClass (Fin K)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => oracle.choose (empMean omega))
```

But I would not add `[MeasurableSingletonClass (Fin K)]` unless Lean asks for it.

---

## Intended proof route

Preferred robust proof:

```lean
by
  have hvec :
      Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat)) :=
    ETC.measurable_empMeanVector_of_forall_measurable empMean hmeas_coord

  exact
    ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
      oracle empMean hvec
```

If argument inference is fragile, use named arguments:

```lean
by
  have hvec :
      Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat)) :=
    ETC.measurable_empMeanVector_of_forall_measurable
      (empMean := empMean) hmeas_coord

  exact
    ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
      (oracle := oracle)
      (empMean := empMean)
      hvec
```

No unfolding of `ETC.CommitOracle` should be needed.

---

## Local APIs/imports

Use the same file as the previous measurability leaf, presumably:

```lean
BanditRLProof.Algorithms.ETCMeasurability
```

Local declarations consumed:

```lean
ETC.measurable_empMeanVector_of_forall_measurable
ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
ETC.CommitOracle
```

Mathlib-facing APIs indirectly used by the existing bridge:

```lean
measurable_pi_lambda
Measurable.of_discrete
MeasurableSingletonClass.toDiscreteMeasurableSpace
```

Mathlib documentation records `MeasurableSingletonClass` as the mixin asserting measurable singletons and includes `MeasurableSet.singleton`; it also records the route from measurable singletons plus countability to `DiscreteMeasurableSpace`, and `Measurable.of_discrete` for arbitrary functions out of a discrete measurable domain. ([Lean Community][1]) The `measurable_pi_lambda` theorem is also tracked in the Mathlib theorem changelog, with later file-split/name-maintenance changes, which matches the already-compiled local use. ([Mathlib Changelog][2])

---

## Regularity contracts

This leaf requires only:

```lean
[MeasurableSpace Omega]
[MeasurableSpace Rat]
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K -> Rat)]
[Countable (Fin K -> Rat)]
```

and the coordinatewise empirical-mean measurability contract:

```lean
forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)
```

It does **not** require:

```lean
Measure Omega
MeasureTheory.IsProbabilityMeasure
MeasurableSingletonClass Rat
MeasurableSpace (Fin K -> Rat) -- unless forced by the existing local bridge
oracle argmax correctness
best-arm uniqueness
independence
filtration
integrability
tail bounds
concentration
```

The theorem states only measurability of the random committed arm induced by `oracle.choose`. It does not claim the oracle is an argmax oracle.

---

## Status

```text
Status: project-local
```

This is not a theorem-card-only task. It should be a short compiled wrapper.

It is not a Mathlib candidate because it depends on project-specific objects:

```lean
ETC.CommitOracle
FiniteBanditModel -- indirectly downstream, not here
```

It is not an import-route card.

---

## Failure policy

If the proof fails:

1. Run:

   ```lean
   #check ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
   #check ETC.measurable_empMeanVector_of_forall_measurable
   ```

2. Mirror the exact typeclass telescope of `ETC.measurable_commitOracle_choose_of_measurable_empMeanVector`.

3. If there is an instance mismatch on `Measurable (fun omega => (empMean omega : Fin K -> Rat))`, do **not** force the proof with `change` or arbitrary measurable-space assumptions. First remove any local:

   ```lean
   [MeasurableSpace (Fin K -> Rat)]
   ```

   and let `[MeasurableSpace Rat]` synthesize the Pi measurable space.

4. If Lean asks for:

   ```lean
   [MeasurableSingletonClass (Fin K)]
   ```

   add it only because the existing local bridge requires it, not because Candidate A logically needs it.

5. Do not unfold `oracle.choose`, do not build a concrete argmax oracle, and do not introduce probability or concentration imports.

---

## Do not attempt in the same batch

Do **not** attempt Candidate B in this batch. It is the natural next leaf after Candidate A, but it composes one additional wrapper: oracle-choice measurability into wrong-event measurability.

Do **not** attempt Candidate C. A concrete finite argmax route card is design work, not the next local proof step.

Do **not** attempt Candidate D. Pairwise-tail import contracts are concentration/probability-facing route design and should wait until the coordinate-to-wrong-event measurable façade is saturated.

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html "Mathlib.MeasureTheory.MeasurableSpace.Defs"
[2]: https://mathlib-changelog.org/v4/theorem/measurable_pi_lambda "Mathlib Changelog v4"
