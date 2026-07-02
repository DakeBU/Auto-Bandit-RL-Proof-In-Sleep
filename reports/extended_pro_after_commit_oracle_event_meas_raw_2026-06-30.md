## Verdict on the completed leaf

`ETC.measurableSet_commitOracle_ne_bestArm` is a reasonable leaf. It is correctly scoped: it specializes the already compiled `commitArm` wrong-event measurability theorem to the composed oracle choice map, and it keeps the measurability of that composed map as an explicit contract. That is the right abstraction boundary.

The leaf does **not** prove oracle construction, argmax correctness, empirical-mean concentration, or final ETC regret. That is good. Its remaining obligation is now sharply exposed:

```lean
Measurable (fun omega : Omega => oracle.choose (empMean omega))
```

So the next leaf should target this contract, not concentration and not concrete argmax construction.

## Selected next leaf

Choose **Candidate C**:

```text
ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-ROUTE-CARD
```

Key decision: **do not wait for a concrete argmax implementation to prove the measurability bridge**. For the current `Rat`-valued finite score-vector setting, the selector map

```lean
oracle.choose : (Fin K -> Rat) -> Fin K
```

can be made measurable by treating the score-vector domain as a countable measurable space with measurable singletons. This is not “arbitrary measurability for free”; it is the specific Mathlib route through `measurable_of_countable`, whose source-space assumptions must be explicit. Mathlib’s statement of `measurable_of_countable` requires a countable source type and `MeasurableSingletonClass` on the source. ([leanprover-community.github.io][1])

## Exact Lean-facing statement

Target theorem-card statement:

```lean
theorem ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)]
    [MeasurableSpace (Fin K -> Rat)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_emp :
      Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))) :
    Measurable (fun omega : Omega => oracle.choose (empMean omega))
```

Intended proof skeleton:

```lean
by
  have hchoose :
      Measurable (fun score : Fin K -> Rat => oracle.choose score) :=
    measurable_of_countable _
  exact hchoose.comp hmeas_emp
```

This theorem is the direct bridge needed by the completed leaf:

```lean
have hmeas_choose :
    Measurable (fun omega : Omega => oracle.choose (empMean omega)) :=
  ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
    oracle empMean hmeas_emp
```

Then the existing theorem applies:

```lean
exact
  ETC.measurableSet_commitOracle_ne_bestArm
    model oracle empMean hmeas_choose
```

## Local APIs / imports

Use the current local file as base:

```lean
import BanditRLProof.Algorithms.ETCMeasurability
```

Likely Mathlib imports:

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Countable.Basic
```

`Mathlib.MeasureTheory.MeasurableSpace.Pi` is relevant because the empirical mean should eventually be treated as a measurable map into the finite product score space `(Fin K -> Rat)`. Its documented role is indexed product σ-algebras and projection-generated product measurability. ([leanprover-community.github.io][2])

## Intended proof route

1. Treat the score vector as a single random variable:

   ```lean
   fun omega : Omega => (empMean omega : Fin K -> Rat)
   ```

2. Assume or derive its measurability:

   ```lean
   hmeas_emp :
     Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))
   ```

3. Prove the oracle selector is measurable as a map out of the countable score-vector space:

   ```lean
   Measurable (fun score : Fin K -> Rat => oracle.choose score)
   ```

   via:

   ```lean
   measurable_of_countable _
   ```

4. Compose.

No argmax correctness is needed for this theorem. The argmax proof belongs to Candidate A later.

## Regularity contracts

Required now:

```lean
[MeasurableSpace Omega]
[MeasurableSpace (Fin K)]
[MeasurableSpace (Fin K -> Rat)]
[MeasurableSingletonClass (Fin K -> Rat)]
[Countable (Fin K -> Rat)]
```

Required from the empirical-mean side:

```lean
Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))
```

If the current empirical-mean theorem is only coordinatewise, add a later bridge:

```lean
theorem ETC.measurable_empMeanVector_of_forall_measurable
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    [MeasurableSpace (Fin K -> Rat)]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))
```

That should be a separate dependency leaf only if needed.

## Retrieval evidence

Mathlib evidence supports the selected route:

| Need                                                                           | Evidence                                                                                                                                                                        |
| ------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Measurability of arbitrary maps out of a countable measurable singleton source | `measurable_of_countable` is available with `[Countable α]` and `[MeasurableSingletonClass α]` on the source. ([leanprover-community.github.io][1])                             |
| Product score-vector measurable space                                          | `Mathlib.MeasureTheory.MeasurableSpace.Pi` documents product σ-algebra generation by projections. ([leanprover-community.github.io][2])                                         |
| Future concrete argmax route, not this batch                                   | `List.argmax` exists, returns an `Option`, has first-occurrence tie-breaking, and has correctness lemmas such as `List.le_of_mem_argmax`. ([leanprover-community.github.io][3]) |

No LML or concentration declaration is needed for Candidate C.

## Status

```text
ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-ROUTE-CARD
```

Status: **theorem-card-only now**, with a strong **project-local compiled candidate** immediately after the card if instance search confirms:

```lean
ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
```

Classification:

```text
project-local / Mathlib-backed
```

Not an imported theorem, not a port candidate, not a Mathlib contribution candidate.

## Failure policy

If the statement fails to compile:

1. **Do not** weaken the theorem to assume `hmeas_choose` again. That would duplicate the previous boundary.
2. If `Countable (Fin K -> Rat)` does not synthesize, add it explicitly as an assumption first; only later consider a local instance lemma.
3. If `MeasurableSingletonClass (Fin K -> Rat)` does not synthesize, keep it explicit in the bridge theorem rather than proving Pi-singleton measurability in the same batch.
4. If vector measurability is missing, stop and make the next leaf the coordinate-to-vector empirical-mean measurability bridge.
5. If the project later switches from `Rat` scores to `Real` scores, this countable-domain route no longer applies. Then the correct route is a concrete recursive/list argmax plus `Measurable.ite` and measurable comparison sets, not `measurable_of_countable`.

## Do not attempt in the same batch

Do **not** attempt Candidate A in this batch. Concrete argmax construction and tie-breaking should remain separate from the measurability discharge.

Do **not** attempt Candidate B in this batch. Pairwise empirical-mean tail imports enter concentration, independence, filtration, and integrability contracts. The current blocker is the deterministic measurability of `oracle.choose ∘ empMean`, not a tail bound.

Do **not** jump to ETC regret or concentration. The next exact local gap is the oracle-choice measurability bridge.

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Basic.html "Mathlib.MeasureTheory.MeasurableSpace.Basic"
[2]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Pi.html "Mathlib.MeasureTheory.MeasurableSpace.Pi"
[3]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/MinMax.html "Mathlib.Data.List.MinMax"
