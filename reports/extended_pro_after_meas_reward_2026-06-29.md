# Extended Pro review after MEAS-REWARD

I’ll use `MEAS-REWARD` as the compiled bridge and pick one pre-expectation leaf, checking finite-sum measurability while minimizing new imports.

I’ll also avoid an omega-dependent filtered `Finset` in the next measurable-function statement, so the leaf stays compile-friendly before measurable regret.

Thought for 7m 42s

## 1. Review of MEAS-REWARD

`MEAS-REWARD` is reasonable as implemented. Do not adjust it before building on it.

The statement is at the right abstraction level:

```lean
Measurable
  (({omega : Omega | action omega t = a} : Set Omega).indicator
    (fun omega : Omega => reward omega t))
```

It avoids integration, probability measures, filtrations, `Rat`/`Real`, and `[DecidableEq Action]`. That is exactly what this layer should do. Mathlib exposes `Measurable.indicator` in the measurable-space basic layer, so the import boundary remains appropriate.

## 2. Single best next executable leaf

Do a finite-sum measurability leaf for selected reward sums.

Recommended new local row:

```text
MEAS-SELECTED-REWARD-FINITE-SUM
```

Do not move next to:

```text
MEAS-REGRET
EXP-INDICATOR-PULL
MEAS-HISTORY
MEAS-POLICY
```

Reason: the current layer has measurability of one selected reward contribution. The next dependency should show that a finite sum of such contributions is measurable. That probes finite sums plus measurable addition, while still avoiding integration/probability/filtration.

## 3. Exact Lean-facing leaf

File:

```text
BanditRLProof/MeasurableSums.lean
```

Then import it from:

```text
BanditRLProof.lean
```

Imports:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasureFoundation
```

`Mathlib.Algebra.BigOperators.Group.Finset.Basic` provides finite-sum APIs such as `Finset.sum_insert`; `Mathlib.MeasureTheory.Group.Arithmetic` provides the measurable-addition typeclass `MeasurableAdd₂` and the dot lemma `Measurable.add`.

Theorem name:

```lean
measurable_finset_sum_indicator_reward
```

Exact statement and proof:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasureFoundation

namespace BanditRLProof

theorem measurable_finset_sum_indicator_reward
    {Omega : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [AddCommMonoid Reward] [MeasurableAdd₂ Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (s : Finset Nat) :
    Measurable
      (fun omega : Omega =>
        s.sum
          (fun t : Nat =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (fun omega' : Omega => reward omega' t)) omega)) := by
  refine Finset.induction_on s ?h_empty ?h_insert
  · simp
  · intro t s ht ih
    have hterm :
        Measurable
          (fun omega : Omega =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (fun omega' : Omega => reward omega' t)) omega) := by
      exact measurable_actionTrace_eval_eq_indicator_reward
        action reward haction hreward a t
    simpa [Finset.sum_insert, ht] using hterm.add ih

end BanditRLProof
```

This is intentionally over arbitrary `s : Finset Nat`, not only `Finset.range t`. The range-specialized use case is immediate by instantiating:

```lean
s := Finset.range t
```

The arbitrary-finset version is also more reusable for stopped prefixes, filtered histories, or later finite windows.

## 4. Local APIs to reuse

Reuse exactly:

```lean
measurable_actionTrace_eval_eq_indicator_reward
```

Do not unfold the event proof again, and do not reprove indicator measurability.

The dependency route should be:

```text
measurableSet_actionTrace_eval_eq
        ↓
measurable_actionTrace_eval_eq_indicator_reward
        ↓
measurable_finset_sum_indicator_reward
```

This creates a clean vertical chain in the probability foundation.

## 5. Mathlib APIs to probe

Use:

```lean
Measurable.add
Finset.induction_on
Finset.sum_insert
```

`Finset.sum_insert` has the additive shape:

```lean
a ∉ s ->
  ∑ x in insert a s, f x = f a + ∑ x in s, f x
```

under `[AddCommMonoid M]`.

The measurable-addition theorem is supplied through `MeasurableAdd₂`; this is the right contract for a generic measurable additive codomain.

## 6. Regularity contracts

Use these contracts:

```lean
[MeasurableSpace Omega]
[MeasurableSpace Action]
[MeasurableSingletonClass Action]
[MeasurableSpace Reward]
[AddCommMonoid Reward]
[MeasurableAdd₂ Reward]
```

plus process measurability:

```lean
haction : forall t : Nat, Measurable (fun omega : Omega => action omega t)
hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t)
```

Do not add:

```lean
[DecidableEq Action]
[Fintype Action]
Measure Omega
ProbabilityMeasure Omega
IsProbabilityMeasure μ
Integrable
Rat
Real
Filtration
```

The absence of `[DecidableEq Action]` remains important: the theorem is still phrased using `Set.indicator`, not a computable `if`.

## 7. Status classification

Classify this as:

```text
MEAS-SELECTED-REWARD-FINITE-SUM: executable local measure-foundation leaf
```

It should be recorded as a prerequisite for later:

```text
MEAS-REGRET
EXP-REGRET-PULLCOUNT
reward-sum concentration leaves
empirical-mean leaves
```

It should not close:

```text
MEAS-REGRET
EXP-INDICATOR-PULL
EXP-REGRET-PULLCOUNT
COND-EXPECT-REWARD
MART-DIFF-REWARD
```

This is a measurable finite-sum bridge, not an expectation or martingale theorem.

## 8. Failure policy

Use a fail-closed policy.

If the theorem fails:

1. First check that the new file imports:

```lean
import Mathlib.MeasureTheory.Group.Arithmetic
```

because `Measurable.add` and `MeasurableAdd₂` live there.

2. If the insertion step is brittle, replace:

```lean
simpa [Finset.sum_insert, ht] using hterm.add ih
```

with:

```lean
have hadd :
    Measurable
      (fun omega : Omega =>
        (({omega' : Omega | action omega' t = a} : Set Omega).indicator
          (fun omega' : Omega => reward omega' t)) omega
        +
        s.sum
          (fun u : Nat =>
            (({omega' : Omega | action omega' u = a} : Set Omega).indicator
              (fun omega' : Omega => reward omega' u)) omega)) :=
  hterm.add ih
simpa [Finset.sum_insert, ht] using hadd
```

3. If typeclass inference complains about measurable addition, keep `[MeasurableAdd₂ Reward]`. Do not specialize to `Rat` or `Real`.
4. Do not import integration, probability, kernels, filtrations, or all of Mathlib.
5. Do not replace this with an expectation statement.

Mark the row complete only after:

```bash
python3 tools\bandit.py check
```

passes.

## 9. Minimal batch before asking again

Complete only:

```text
MEAS-SELECTED-REWARD-FINITE-SUM
```

with:

```text
BanditRLProof/MeasurableSums.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
unfinished/docs/index refresh
python3 tools\bandit.py check
```

Then stop and ask again. The next review should decide between a `sumRewards`-specific measurability corollary and the first expectation canary.
