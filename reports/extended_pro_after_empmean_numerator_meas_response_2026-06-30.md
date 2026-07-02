## 1. Selected leaf

**Candidate A:**

```text
ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION-OF-DIV-CONST
```

This is the correct next leaf. The numerator measurability theorem is now compiled, and the scratch proof shows the full empirical-mean measurability theorem works under an explicit division-by-constant contract. This moves the new `ETC.empMeanAtExploration` API forward while deliberately postponing the exact Mathlib/Rat division-measurability import decision.

Candidate B should be a follow-up only after this wrapper exists. Candidate C and D are premature.

---

## 2. Exact Lean-facing statement

```lean
theorem ETC.measurable_empMeanAtExploration_of_measurable_div_const
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (hdiv_const : forall c : Rat, Measurable (fun x : Rat => x / c)) :
    Measurable (fun omega : Omega =>
      ETC.empMeanAtExploration spec commitArm (reward omega) a) := by
  have hnum : Measurable (fun omega : Omega =>
      sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K)) :=
    ETC.measurable_sumRewards_actionWithCommit_exploration
      spec commitArm a reward hreward

  have hdiv : Measurable (fun omega : Omega =>
      sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K) /
        (pullCount (ETC.actionWithCommit spec commitArm) a
          (spec.explorationPulls * K) : Rat)) := by
    exact (hdiv_const _).comp hnum

  simpa [ETC.empMeanAtExploration] using hdiv
```

If placed inside `namespace ETC`, use:

```lean
theorem measurable_empMeanAtExploration_of_measurable_div_const
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (hdiv_const : forall c : Rat, Measurable (fun x : Rat => x / c)) :
    Measurable (fun omega : Omega =>
      empMeanAtExploration spec commitArm (reward omega) a) := by
  have hnum : Measurable (fun omega : Omega =>
      sumRewards (actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K)) :=
    measurable_sumRewards_actionWithCommit_exploration
      spec commitArm a reward hreward

  have hdiv : Measurable (fun omega : Omega =>
      sumRewards (actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K) /
        (pullCount (actionWithCommit spec commitArm) a
          (spec.explorationPulls * K) : Rat)) := by
    exact (hdiv_const _).comp hnum

  simpa [empMeanAtExploration] using hdiv
```

---

## 3. Local APIs / imports

Required local APIs:

```lean
ETC.empMeanAtExploration
ETC.measurable_sumRewards_actionWithCommit_exploration
ETC.actionWithCommit
sumRewards
pullCount
RewardTrace
```

Likely project import:

```lean
import BanditRLProof.Algorithms.ETCTraceCountLemmas
```

or whichever local file currently exports both:

```lean
ETC.empMeanAtExploration
ETC.measurable_sumRewards_actionWithCommit_exploration
```

Mathlib-side APIs used:

```lean
Measurable.comp
```

No new division-measurability import is required, because the theorem takes:

```lean
hdiv_const : forall c : Rat, Measurable (fun x : Rat => x / c)
```

as an explicit contract.

Mathlib’s measurable-space API documents `Measurable` and function composition for measurable maps, which is exactly the structure used by `(hdiv_const _).comp hnum`. ([Lean Community][1])

---

## 4. Intended proof route

The proof has three steps.

First, obtain numerator measurability from the compiled local theorem:

```lean
have hnum : Measurable (fun omega : Omega =>
    sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
      (spec.explorationPulls * K)) :=
  ETC.measurable_sumRewards_actionWithCommit_exploration
    spec commitArm a reward hreward
```

Second, compose numerator measurability with the explicit division-by-constant measurable map:

```lean
have hdiv : Measurable (fun omega : Omega =>
    sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
      (spec.explorationPulls * K) /
      (pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K) : Rat)) := by
  exact (hdiv_const _).comp hnum
```

Here the constant is inferred as:

```lean
(pullCount (ETC.actionWithCommit spec commitArm) a
  (spec.explorationPulls * K) : Rat)
```

Third, unfold the empirical-mean definition:

```lean
simpa [ETC.empMeanAtExploration] using hdiv
```

This proof should match the scratch theorem almost verbatim.

---

## 5. Regularity contracts

Keep exactly these regularity assumptions:

```lean
[MeasurableSpace Omega]
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
[MeasurableSpace Rat]
[MeasurableAdd₂ Rat]
```

and the reward-coordinate measurability assumption:

```lean
hreward : forall t : Nat,
  Measurable (fun omega : Omega => reward omega t)
```

and the explicit division contract:

```lean
hdiv_const : forall c : Rat, Measurable (fun x : Rat => x / c)
```

Do **not** add:

```lean
Measure Omega
mu : Measure Omega
[IsProbabilityMeasure mu]
[MeasurableDiv Rat]
hexplorationPulls_pos
denominator nonzero
commit argmax
pairwise tail assumptions
independence
sub-Gaussianity
filtration
conditional expectation
```

The denominator nonzero theorem is not needed for measurability because `Rat` division is total. It will be used later for algebraic normalization, not for this leaf.

---

## 6. Retrieval evidence

**Local evidence:** the prompt gives a scratch proof that compiles with exactly this theorem shape. It also confirms the compiled local numerator theorem:

```lean
ETC.measurable_sumRewards_actionWithCommit_exploration
```

which supplies `hnum`.

**Mathlib evidence:** Mathlib’s measurable-space documentation confirms that measurable maps are closed under composition via the standard measurable-function API; the proof uses exactly this through `(hdiv_const _).comp hnum`. ([Lean Community][1])

**No LML/concentration evidence:** this leaf does not involve Hoeffding, sub-Gaussian concentration, independence, martingales, filtrations, or conditional expectation.

---

## 7. Status

**Status:** project-local.

This is a local wrapper around:

```lean
ETC.empMeanAtExploration
ETC.measurable_sumRewards_actionWithCommit_exploration
```

with an explicit division-by-constant measurability contract.

It is not imported, not a Mathlib candidate, not a port candidate, and not theorem-card-only.

---

## 8. Failure policy

Implement exactly Candidate A. If it fails, repair only this wrapper.

Recommended repair sequence:

1. Keep the proof identical to the scratch version first.

2. If namespace qualification fails, switch between:

```lean
ETC.empMeanAtExploration
ETC.actionWithCommit
ETC.measurable_sumRewards_actionWithCommit_exploration
```

and unqualified names inside `namespace ETC`.

3. If `(hdiv_const _).comp hnum` fails to infer the constant, make it explicit:

```lean
have hdivConst :
    Measurable (fun x : Rat =>
      x / (pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K) : Rat)) :=
  hdiv_const
    (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat)

exact hdivConst.comp hnum
```

4. If `simpa [ETC.empMeanAtExploration] using hdiv` fails, use:

```lean
change Measurable (fun omega : Omega =>
  sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
      (spec.explorationPulls * K) /
    (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat))
exact hdiv
```

5. Do not add a Mathlib division-measurability import in this batch unless the existing imports cannot even parse `Measurable`. The point of this leaf is to avoid that import decision by taking `hdiv_const` explicitly.

6. Stop after this theorem compiles. Do not implement division wrapper, argmax wiring, concentration route, or final ETC theorem in the same batch.

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html?utm_source=chatgpt.com "Mathlib.MeasureTheory.MeasurableSpace.Defs"
