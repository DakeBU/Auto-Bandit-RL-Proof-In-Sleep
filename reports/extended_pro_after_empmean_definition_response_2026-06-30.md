# Extended Pro Review After ETC Empirical Mean Definition

## 1. Selected leaf

**Candidate A: numerator measurability only.**

Leaf id:

```text
ETC-MEASURABLE-SUMREWARDS-ACTION-WITH-COMMIT-EXPLORATION
```

This is the right next step because it connects the new deterministic empirical-mean API to the stochastic `Omega -> RewardTrace Rat` setting without yet requiring a division-measurability import or a `Rat` empirical-mean measurability theorem.

Candidate B is a good follow-up after this compiles. Candidate C is useful only if B fails on the exact Mathlib division API. Candidate D is premature because argmax/commit wiring should consume a stable measurable empirical-mean map, not just the deterministic definition.

---

## 2. Exact Lean-facing statement

```lean
theorem ETC.measurable_sumRewards_actionWithCommit_exploration
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K))
```

If the theorem is placed inside `namespace ETC`, drop the `ETC.` prefix only where local style requires it:

```lean
theorem measurable_sumRewards_actionWithCommit_exploration
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      sumRewards (actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K))
```

---

## 3. Local APIs / imports

Required local API:

```lean
measurable_sumRewards
ETC.actionWithCommit
sumRewards
RewardTrace
```

Likely import location:

```lean
import BanditRLProof.Algorithms.ETCTraceCountLemmas
```

or the local file that exports:

```lean
sumRewards
RewardTrace
measurable_sumRewards
```

Mathlib-side concepts used are ordinary `Measurable`, `Measurable.comp`, `measurable_const`, and singleton-measurability support for equality tests in the recursive reward sum. Mathlib's measurable-space documentation explicitly exposes `Measurable`, `Measurable.comp`, and `measurable_const`, and defines measurability as preimage preservation of measurable sets. It also lists `MeasurableSingletonClass` and `MeasurableSet.singleton`, which are the standard contracts used when measurability proofs inspect equality with a fixed action.

No `Measure`, `ENNReal`, probability, concentration, or division import should be introduced for this leaf.

---

## 4. Intended proof route

Use `measurable_sumRewards` with a stochastic action trace that is constant in `omega`:

```lean
fun _ : Omega => ETC.actionWithCommit spec commitArm
```

The action-coordinate measurability obligation should be discharged by `measurable_const`.

Proof skeleton, assuming `measurable_sumRewards` takes stochastic action/reward traces:

```lean
by
  have haction :
      forall t : Nat,
        Measurable
          (fun omega : Omega =>
            (ETC.actionWithCommit spec commitArm) t) := by
    intro t
    exact measurable_const

  simpa using
    (measurable_sumRewards
      (action := fun _ : Omega => ETC.actionWithCommit spec commitArm)
      (reward := reward)
      (a := a)
      (t := spec.explorationPulls * K)
      haction hreward)
```

If the local theorem uses positional rather than named arguments, use:

```lean
by
  have haction :
      forall t : Nat,
        Measurable
          (fun omega : Omega =>
            (ETC.actionWithCommit spec commitArm) t) := by
    intro t
    exact measurable_const

  simpa using
    measurable_sumRewards
      (fun _ : Omega => ETC.actionWithCommit spec commitArm)
      reward haction hreward a (spec.explorationPulls * K)
```

If `measurable_sumRewards` was instead specialized to deterministic action traces, the proof is even smaller:

```lean
by
  simpa using
    measurable_sumRewards
      (action := ETC.actionWithCommit spec commitArm)
      (reward := reward)
      (a := a)
      (t := spec.explorationPulls * K)
      hreward
```

Use the stochastic-action version first because the prompt's local observation says the existing route is through the constant action trace.

---

## 5. Regularity contracts

Keep exactly the contracts needed by `measurable_sumRewards`:

```lean
[MeasurableSpace Omega]
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
[MeasurableSpace Rat]
[MeasurableAdd₂ Rat]
```

and the reward-coordinate measurability assumption:

```lean
(hreward : forall t : Nat,
  Measurable (fun omega : Omega => reward omega t))
```

Do **not** add:

```lean
Measure Omega
mu : Measure Omega
[IsProbabilityMeasure mu]
MeasurableDiv Rat
hdiv_const
hexplorationPulls_pos
commit-arm argmax assumptions
independence
sub-Gaussianity
filtration
conditional expectation
pairwise tail bounds
```

Also do not rewrite the denominator or mention `empMeanAtExploration` in the theorem statement. This leaf is numerator-only.

---

## 6. Retrieval evidence

**Local declaration evidence from the prompt:**

The prompt says `measurable_sumRewards` is already compiled locally and that the numerator route appears to work by applying it to:

```lean
fun _ : Omega => ETC.actionWithCommit spec commitArm
```

and:

```lean
reward : Omega -> RewardTrace Rat
```

That is exactly Candidate A's structure.

**Mathlib evidence:**

Mathlib has the core measurable-function infrastructure needed for the wrapper: `Measurable`, `Measurable.comp`, and `measurable_const` are exposed in `Mathlib.MeasureTheory.MeasurableSpace.Defs`. Mathlib's measurable-space docs also state that a function is measurable when preimages of measurable sets are measurable, matching the local theorem's proof style for recursive measurable constructions.

**LML evidence:**

No LML/Hoeffding/concentration result is needed or relevant for this leaf.

---

## 7. Status

**Status:** project-local.

This is a local wrapper around the project's `measurable_sumRewards` theorem and the ETC action trace. It is not imported, not a Mathlib candidate, not a port candidate, and not theorem-card-only.

---

## 8. Failure policy

If the selected leaf fails, repair only the numerator-measurability wrapper.

Recommended sequence:

1. Inspect the exact local declaration:

```bash
python3 tools/bandit.py list-lean-decls measurable_sumRewards --statement
```

2. If the theorem expects stochastic action traces, use:

```lean
(action := fun _ : Omega => ETC.actionWithCommit spec commitArm)
```

with:

```lean
have haction : forall t : Nat,
    Measurable (fun omega : Omega =>
      (ETC.actionWithCommit spec commitArm) t) := by
  intro t
  exact measurable_const
```

3. If the theorem expects deterministic action traces, pass:

```lean
(action := ETC.actionWithCommit spec commitArm)
```

and remove `haction`.

4. If named arguments fail, switch to positional arguments after reading the declaration.

5. If `Rat` measurability or addition instances are already inferred, keep the explicit assumptions anyway unless they cause instance conflicts; if they do, remove only the redundant explicit instance arguments.

6. If imports fail, add the narrow local file that exports `measurable_sumRewards`. Do not add division-measurability imports in this batch.

Stop after this theorem compiles. Do not implement Candidate B, C, or D in the same batch.

---

## Assessment of the compiled empirical-mean definition

The compiled deterministic `ETC.empMeanAtExploration` definition was a reasonable step after the Rat nonzero denominator adapter. The chain now has a clean separation:

```text
deterministic pull count
-> Nat/Rat denominator positivity and nonzero facts
-> deterministic empirical mean at the exploration horizon
-> numerator measurability for stochastic reward traces
```

For bookkeeping, after this numerator leaf compiles, mirror the usual gate:

```text
lake build BanditRLProof.Algorithms.ETCTraceCountLemmas
lake build Tests
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-lean-decls ETC.measurable_sumRewards_actionWithCommit_exploration --statement
python3 tools/bandit.py check
python3 tools/bandit.py unfinished
```

If the empirical-mean definition batch did not already run `reference-index`, `review-status`, and `unfinished`, run those as a documentation/check synchronization step before moving to division measurability.
