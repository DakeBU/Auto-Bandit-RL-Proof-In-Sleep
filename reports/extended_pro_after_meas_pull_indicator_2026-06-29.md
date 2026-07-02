# Extended Pro review after MEAS-PULL-INDICATOR

I’ll treat the existing compiled state as fixed and choose one next leaf that strengthens the probability/measurability layer without forcing integration or algorithm-specific commitments.

The current indicator theorem looks usable as-is. I’m now weighing a minimal integration canary against one more measurability-only bridge, with Mathlib API compatibility deciding the leaf.

Thought for 7m 6s

## 1. Review of MEAS-PULL-INDICATOR

`MEAS-PULL-INDICATOR` is reasonable as implemented. I would not adjust the statement before building on it.

The theorem has the right abstraction level:

```lean
Measurable
  (({omega : Omega | action omega t = a} : Set Omega).indicator
    (fun _ : Omega => c))
```

It avoids premature choices about `Rat`, `Real`, `ENNReal`, probability measures, or integration. It also correctly avoids `[DecidableEq Action]` by using `Set.indicator` rather than a computable `if action omega t = a then ... else ...`.

The import boundary is also right: `Mathlib.MeasureTheory.MeasurableSpace.Basic` exposes `Measurable.indicator`, and the theorem itself only needs measurable spaces, singleton measurability, a zero value in the codomain, and constant measurability. Mathlib’s docs list `Measurable.indicator` with the expected contract: measurable function plus measurable set gives measurability of the indicator.

## 2. Single best next executable leaf

Do `MEAS-REWARD`, but make it the selected-reward indicator measurability leaf, not a trivial restatement that `reward omega t` is measurable.

Recommended row:

```text
MEAS-REWARD
```

Recommended theorem:

```text
measurable_actionTrace_eval_eq_indicator_reward
```

This is the next useful bridge:

```text
1{A_t = a} * R_t is measurable
```

in `Set.indicator` form. It directly extends the event/indicator layer and prepares later finite reward sums, empirical means, and expectation identities without importing integration yet.

Do not do `EXP-INDICATOR-PULL` next. That would force the project to choose an integration/expectation scalar route. Do not do `MEAS-REGRET` yet either; regret measurability will need finite sums, gap measurability, and likely `Rat`/`Real` Borel import decisions.

## 3. Exact next Lean leaf

File:

```text
BanditRLProof/MeasureFoundation.lean
```

Imports:

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import BanditRLProof.Core
```

`MeasurableSpace.Basic` already provides `Measurable.indicator` and `Measurable.ite`; `Measurable.indicator` is the intended API here.

Statement shape:

```lean
namespace BanditRLProof

theorem measurable_actionTrace_eval_eq_indicator_reward
    {Omega : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [Zero Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (t : Nat) :
    Measurable
      (({omega : Omega | action omega t = a} : Set Omega).indicator
        (fun omega : Omega => reward omega t)) := by
  exact Measurable.indicator (hreward t)
    (measurableSet_actionTrace_eval_eq action haction a t)

end BanditRLProof
```

More explicit fallback proof:

```lean
theorem measurable_actionTrace_eval_eq_indicator_reward
    {Omega : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [Zero Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (t : Nat) :
    Measurable
      (({omega : Omega | action omega t = a} : Set Omega).indicator
        (fun omega : Omega => reward omega t)) := by
  exact Measurable.indicator
    (s := {omega : Omega | action omega t = a})
    (f := fun omega : Omega => reward omega t)
    (hreward t)
    (measurableSet_actionTrace_eval_eq action haction a t)
```

## 4. APIs to reuse/probe

Local APIs:

```lean
measurableSet_actionTrace_eval_eq
```

Do not unfold the event proof again. This theorem is precisely the compiled local interface for pull/action event measurability.

You do not need to reuse:

```lean
measurable_actionTrace_eval_eq_indicator_const
```

The new theorem is a variable-reward version of the same `Measurable.indicator` pattern.

Mathlib APIs:

```lean
Measurable.indicator
```

with this conceptual shape:

```lean
Measurable f ->
MeasurableSet s ->
Measurable (s.indicator f)
```

## 5. Regularity contracts

The intended contracts are exactly:

```lean
[MeasurableSpace Omega]
[MeasurableSpace Action]
[MeasurableSingletonClass Action]
[MeasurableSpace Reward]
[Zero Reward]
```

plus the explicit process measurability hypotheses:

```lean
haction : forall t : Nat, Measurable (fun omega : Omega => action omega t)
hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t)
```

Do not add:

```lean
[DecidableEq Action]
[Fintype Action]
[MeasurableSingletonClass Reward]
Measure Omega
ProbabilityMeasure Omega
IsProbabilityMeasure μ
Integrable
AddMonoid Reward
TopologicalSpace Reward
BorelSpace Reward
Rat
Real
Filtration
```

The theorem is only about measurability of a selected reward contribution. It should stay independent of probability measures, expectations, and reward algebra.

## 6. Status classification

Classify this as:

```text
MEAS-REWARD: executable missing-leaf candidate
```

More precisely:

```text
MEAS-REWARD / selected reward indicator measurability
```

Do not treat it as closing any theorem card about expected reward, conditional reward, martingale differences, or concentration. It is a local measurable-function bridge.

If the project’s existing `MEAS-REWARD` row is intended to mean only raw reward-evaluation measurability, then mark this as a stronger local leaf and update the row description. A theorem that merely returns `hreward t` would be too weak to improve the graph.

## 7. Proof route

The proof is one application:

```lean
exact Measurable.indicator (hreward t)
  (measurableSet_actionTrace_eval_eq action haction a t)
```

Expanded dependency route:

`hreward t` proves:

```lean
Measurable (fun omega : Omega => reward omega t)
```

`measurableSet_actionTrace_eval_eq action haction a t` proves:

```lean
MeasurableSet {omega : Omega | action omega t = a}
```

`Measurable.indicator` combines them:

```lean
Measurable
  (({omega | action omega t = a} : Set Omega).indicator
    (fun omega => reward omega t))
```

No induction, finite sums, regret decomposition, expectation, filtration, or concentration theorem should appear in this proof.

## 8. Failure policy

Use a fail-closed policy.

If this leaf fails:

1. Try the explicit `Measurable.indicator` proof with `(s := ...)` and `(f := ...)`.
2. Confirm `[Zero Reward]` and `[MeasurableSpace Reward]` are present.
3. Confirm the existing event theorem is imported through `BanditRLProof.Core`/`MeasureFoundation` as expected.
4. Do not switch to an `if action omega t = a then reward omega t else 0` statement unless you intentionally want to add `[DecidableEq Action]`.
5. Do not import integration, probability, filtration, or all of Mathlib.
6. Do not specialize to `Rat` or `Real` to make inference easier.
7. Do not mark `MEAS-REWARD` complete if the only compiled theorem is the tautology:

```lean
hreward t
```

Mark the row complete only after:

```bash
python3 tools\bandit.py check
```

passes.

## 9. Minimal batch

Complete only:

```text
MEAS-REWARD
```

with:

```text
one theorem in BanditRLProof/MeasureFoundation.lean
one consumer test in Tests/Basic.lean
unfinished-leaf/docs/index refresh
python3 tools\bandit.py check
```

Then stop and ask again. The next decision should be between a finite-sum measurability leaf for selected reward sums and the first expectation/probability identity; do not jump directly to UCB/ETC/concentration.
