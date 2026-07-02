## Review of the completed leaf

The completed leaf is reasonable and correctly scoped.

```lean
theorem ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
```

is a good local consumer theorem because it proves only:

> if the empirical-mean vector is measurable as an object of type `Fin K -> Rat`, then an abstract commit oracle’s chosen arm is measurable.

The use of `measurable_of_countable` is acceptable here because the theorem deliberately treats `oracle.choose` as an arbitrary function on a countable measurable singleton domain. It does **not** claim argmax correctness, tie-breaking correctness, or concentration. The explicit assumptions

```lean
[MeasurableSingletonClass (Fin K -> Rat)]
[Countable (Fin K -> Rat)]
```

are strong but honest. They expose the regularity required to make an arbitrary oracle choice function measurable.

The next missing piece should be the producer-side bridge that supplies the empirical-mean vector measurability assumption.

---

# Selected next leaf: Candidate A

## `ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE`

This is the right next leaf. It is small, local, directly feeds the newest compiled oracle-choice theorem, and does not cross into concrete argmax construction or concentration.

## Corrected Lean-facing statement

The proposed statement should **not** assume an arbitrary

```lean
[MeasurableSpace (Fin K -> Rat)]
```

because coordinatewise measurability only implies measurability into the **Pi/product measurable space**, not into an arbitrary measurable structure on the function type.

Use this corrected statement:

```lean
theorem ETC.measurable_empMeanVector_of_forall_measurable
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))
```

This lets Lean use the standard Pi measurable-space instance for `Fin K -> Rat`.

A slightly more elaboration-stable version is:

```lean
theorem ETC.measurable_empMeanVector_of_forall_measurable
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => fun a : Fin K => empMean omega a)
```

Either form should be equivalent, but the second avoids depending on the cast/annotation elaboration of `(empMean omega : Fin K -> Rat)`.

---

# Local APIs / imports

Likely sufficient existing import context:

```lean
import BanditRLProof.Algorithms.ETCMeasurability
```

or whatever file currently imports the measurable-space API used by the latest theorem.

Mathlib-side API expected:

```lean
measurable_pi_lambda
```

Expected proof shape:

```lean
by
  exact measurable_pi_lambda fun a => hmeas_coord a
```

If the theorem name differs in the local Mathlib snapshot, search for nearby API names:

```bash
grep -R "measurable_pi_lambda" .lake/packages/mathlib/Mathlib/MeasureTheory -n
grep -R "pi_lambda" .lake/packages/mathlib/Mathlib/MeasureTheory -n
grep -R "Measurable.*forall" .lake/packages/mathlib/Mathlib/MeasureTheory -n
```

Possible alternatives in nearby Mathlib APIs may include Pi-measurability lemmas phrased as an iff, but the route remains the same: prove measurability into a Pi type by proving each coordinate projection measurable.

---

# Intended proof route

Use the standard Pi-space characterization:

1. Target:

   ```lean
   Measurable (fun omega : Omega => fun a : Fin K => empMean omega a)
   ```

2. Apply the Pi measurability constructor:

   ```lean
   measurable_pi_lambda
   ```

3. Reduce the proof obligation to every coordinate:

   ```lean
   forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)
   ```

4. Close with the hypothesis:

   ```lean
   hmeas_coord
   ```

Full skeleton:

```lean
theorem ETC.measurable_empMeanVector_of_forall_measurable
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => fun a : Fin K => empMean omega a) := by
  exact measurable_pi_lambda fun a => hmeas_coord a
```

If Lean accepts the original target annotation, this version is also fine:

```lean
theorem ETC.measurable_empMeanVector_of_forall_measurable
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat)) := by
  exact measurable_pi_lambda fun a => hmeas_coord a
```

---

# Regularity contracts

Minimal contracts for this leaf:

```lean
[MeasurableSpace Omega]
[MeasurableSpace Rat]
```

Not needed for this bridge:

```lean
[MeasurableSpace (Fin K)]
[MeasurableSpace (Fin K -> Rat)]
[MeasurableSingletonClass (Fin K -> Rat)]
[Countable (Fin K -> Rat)]
[MeasurableSingletonClass Rat]
[Countable Rat]
```

Those may be needed downstream when composing with:

```lean
ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
```

but they are not needed for coordinate-to-vector measurability itself.

A later combined wrapper could have the larger contract:

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

But that should be a later small corollary, not this batch.

---

# Retrieval evidence

## Mathlib evidence

Relevant imported Mathlib pattern:

```lean
measurable_pi_lambda
```

This is the canonical bridge:

```lean
(forall i, Measurable fun x => f x i)
⊢ Measurable fun x => fun i => f x i
```

This is exactly the shape needed for `Omega -> Fin K -> Rat`.

## Local evidence

The latest compiled theorem consumes precisely this conclusion:

```lean
ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
```

with hypothesis:

```lean
hmeas_emp :
  Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))
```

Therefore Candidate A closes the gap between coordinatewise empirical-mean measurability and oracle-choice measurability.

## LML / project-memory evidence

The current local layer has already moved through:

```lean
ETC.measurable_empMeanAtExploration
ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
ETC.measurableSet_commitOracle_ne_bestArm
```

So the natural next producer-side object is the vector-valued empirical mean, not argmax construction or concentration.

---

# Status

**Status:** project-local.

More precisely:

* The mathematical fact is imported from Mathlib through the Pi-measurability API.
* The exact theorem name should be project-local because it specializes the API to the project’s empirical-mean vector shape.
* It is not theorem-card-only.
* It is not a Mathlib candidate.
* It is not a port candidate.

---

# Failure policy

If the corrected statement fails:

1. First check whether the target accidentally uses an arbitrary local instance:

   ```lean
   [MeasurableSpace (Fin K -> Rat)]
   ```

   Remove it.

2. Prefer the lambda-expanded target:

   ```lean
   Measurable (fun omega : Omega => fun a : Fin K => empMean omega a)
   ```

   rather than the annotation-heavy target:

   ```lean
   Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))
   ```

3. Search Mathlib for the exact Pi API name if `measurable_pi_lambda` is unavailable.

4. If the local Mathlib snapshot has no convenient constructor, route-card the bridge as:

   ```lean
   ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE
   ```

   with proof dependency on the Pi measurable-space constructor/iff.

Do **not** replace this with a concrete finite argmax oracle or a concentration import route.

---

# Candidates not to attempt in this batch

Do not attempt Candidate B in the same batch:

```text
ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD
```

Reason: the abstract oracle layer is still not saturated. The coordinate-to-vector measurability bridge is a direct missing producer for the already compiled oracle-choice theorem.

Do not attempt Candidate C in the same batch:

```text
ETC-PAIRWISE-TAIL-IMPORT-ROUTE-CARD
```

Reason: concentration-tail assumptions sit beyond the current local measurability/oracle boundary. The pairwise-tail probability wrappers already consume abstract `tail`; before importing concentration machinery, the project should finish the local measurability chain.
