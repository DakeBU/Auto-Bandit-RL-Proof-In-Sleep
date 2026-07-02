## 1. Selected leaf

**Candidate A, but with a corrected contract.**

Leaf id:

```text
RAT-MEASURABLE-DIV-CONST-OF-MEASURABLE-SINGLETON
```

Do **not** try to prove

```lean
forall c : Rat, Measurable (fun x : Rat => x / c)
```

under only an arbitrary

```lean
[MeasurableSpace Rat]
```

That is too weak: for an arbitrary measurable structure on `Rat`, not every function `Rat -> Rat` is necessarily measurable. The smallest robust replacement is to add:

```lean
[MeasurableSingletonClass Rat]
```

and use the countability of `Rat`.

---

## 2. Exact Lean-facing statement

Recommended project-local wrapper:

```lean
theorem measurable_rat_div_const
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat]
    (c : Rat) :
    Measurable (fun x : Rat => x / c) := by
  exact measurable_of_countable (fun x : Rat => x / c)
```

If the project prefers a namespace to avoid root-name pollution:

```lean
namespace ABRL

theorem measurable_rat_div_const
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat]
    (c : Rat) :
    Measurable (fun x : Rat => x / c) := by
  exact measurable_of_countable (fun x : Rat => x / c)

end ABRL
```

I would avoid `Rat.measurable_div_const` for now because Mathlib may later add a similarly named theorem.

---

## 3. Local APIs / imports

No ETC-local API is required for this leaf.

Use:

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.Rat.Encodable
```

Why these imports:

```lean
measurable_of_countable
```

is in the measurable-space API and has the relevant shape: if the domain is countable and has measurable singletons, then any function out of it is measurable. Mathlib’s docs list:

```lean
theorem measurable_of_countable
    [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α]
    (f : α → β) :
    Measurable f
```

with the rendered statement showing exactly this contract. ([Lean Community][1])

`Mathlib.Data.Rat.Encodable` supplies the `Encodable ℚ` instance and, as a consequence, the `Countable ℚ` instance. ([Lean Community][2])

The current project import chain may already expose both. If so, add no new import.

---

## 4. Intended proof route

The proof should not use topology, continuity, or field-continuity lemmas.

Use the countable-domain measurability route:

```lean
by
  exact measurable_of_countable (fun x : Rat => x / c)
```

Reason:

* Domain: `Rat`.
* `Rat` is countable via `Mathlib.Data.Rat.Encodable`.
* Domain singletons are measurable by `[MeasurableSingletonClass Rat]`.
* Therefore every function `Rat -> Rat` is measurable, including `fun x => x / c`.

This also handles `c = 0` automatically because the proof does not rely on nonzero division.

---

## 5. Regularity contracts

Use exactly:

```lean
[MeasurableSpace Rat]
[MeasurableSingletonClass Rat]
(c : Rat)
```

Do **not** add:

```lean
MeasurableDiv Rat
MeasurableAdd₂ Rat
TopologicalSpace Rat
BorelSpace Rat
ContinuousDiv
c ≠ 0
Omega
K
ETC.Spec K
RewardTrace Rat
Measure Omega
IsProbabilityMeasure
filtration
conditional expectation
concentration
```

`[BorelSpace Rat]` is a valid alternative under canonical topological/Borel semantics, and Mathlib documents a `Rat.borelSpace` instance. ([Lean Community][3]) But for this leaf, `[MeasurableSingletonClass Rat]` is the smaller and more direct measurable-space contract.

---

## 6. Retrieval evidence

Mathlib evidence:

* `measurable_of_countable` proves measurability of any function from a countable measurable-singleton domain. ([Lean Community][1])
* `Rat` has an `Encodable` instance, yielding `Countable ℚ`. ([Lean Community][2])
* Mathlib’s measurable-space API also defines `DiscreteMeasurableSpace`, `Measurable.of_discrete`, and the instance path from measurable singletons plus countability to a discrete measurable space, which supports the same design choice. ([Lean Community][4])
* Mathlib has a Borel-space instance for `Rat`, but this leaf does not need to use the topological route. ([Lean Community][3])

Local evidence:

* The compiled theorem `ETC.measurable_empMeanAtExploration_of_measurable_div_const` consumes exactly a contract of the form:

```lean
hdiv_const : forall c : Rat, Measurable (fun x : Rat => x / c)
```

This wrapper supplies that contract once `[MeasurableSingletonClass Rat]` is available.

No LML/Hoeffding/sub-Gaussian evidence is relevant for this leaf.

---

## 7. Status

**Status:** project-local import-route wrapper.

It is not a Mathlib candidate: the theorem is a short specialization of existing Mathlib machinery. It is not theorem-card-only. It should compile directly.

---

## 8. Failure policy

Implement exactly this wrapper and stop.

If it fails:

1. Check whether `Countable Rat` is in scope. If not, add:

```lean
import Mathlib.Data.Rat.Encodable
```

2. Check whether `measurable_of_countable` is in scope. If not, add:

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Basic
```

3. If Lean cannot infer `Countable Rat`, make it explicit:

```lean
theorem measurable_rat_div_const
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat]
    [Countable Rat]
    (c : Rat) :
    Measurable (fun x : Rat => x / c) := by
  exact measurable_of_countable (fun x : Rat => x / c)
```

Then try removing `[Countable Rat]` after imports are fixed.

4. If the repository already uses canonical discrete measurable-space instances for countable types, an alternative proof is:

```lean
  exact Measurable.of_discrete
```

but do not switch to that unless `measurable_of_countable` is unavailable.

5. Do not implement the no-`hdiv_const` empirical-mean measurability theorem in this batch. That should be the next leaf after this wrapper compiles.

6. Do not start argmax wiring, pairwise concentration, filtration, conditional expectation, UCB/TS/EXP3/Tsallis/OFUL, or RL/MDP work.

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Basic.html "Mathlib.MeasureTheory.MeasurableSpace.Basic"
[2]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Rat/Encodable.html?utm_source=chatgpt.com "Mathlib.Data.Rat.Encodable"
[3]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.html "Mathlib.MeasureTheory.Constructions.BorelSpace.Basic"
[4]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html "Mathlib.MeasureTheory.MeasurableSpace.Defs"
