# Extended Pro review after MEAS-SELECTED-REWARD-FINITE-SUM

I’ll treat the compiled finite-sum measurability lemma as the base and choose one local consumer next, likely connecting it to `sumRewards` without expectation or filtrations.

I’ll also verify the narrow Mathlib surface needed for that consumer and keep the recommendation to one exact executable statement.

Thought for 10m 25s

## 1. Review of MEAS-SELECTED-REWARD-FINITE-SUM

Yes. The leaf is reasonable as implemented. Do not adjust it before building on it.

The statement is correctly generic over:

```lean
s : Finset Nat
```

rather than being hard-coded to `Finset.range t`. That makes it reusable for finite prefixes, windows, stopped finite sets, and later algorithm-specific sub-sums.

The import boundary is also acceptable:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasureFoundation
```

`Mathlib.MeasureTheory.Group.Arithmetic` is the right boundary for measurable addition: it exposes `Measurable.add` under `[MeasurableAdd₂]`, and it also contains finite-sum measurability APIs such as `Finset.measurable_sum`.

The induction proof is fine. There is no need to rewrite it to use `Finset.measurable_sum` unless you want a later cleanup pass.

## 2. Single best next executable leaf

Do a `sumRewards`-specific measurability corollary next.

Recommended local row:

```text
MEAS-SUMREWARDS
```

Recommended theorem:

```lean
measurable_sumRewards
```

This is the right next bridge because the project now has:

```lean
measurable_finset_sum_indicator_reward
```

but downstream bandit proofs will consume the local deterministic quantity:

```lean
sumRewards (action omega) (reward omega) a n
```

The next leaf should connect those two worlds.

Do not move next to:

```text
MEAS-REGRET
EXP-INDICATOR-PULL
EXP-REGRET-PULLCOUNT
MEAS-HISTORY
MEAS-POLICY
```

`MEAS-REGRET` will require a scalar/regret measurability design. `EXP-*` will force probability measures and integration. History/policy measurability is a separate modeling layer. The next lowest-risk executable step is to show that the already-defined local reward accumulator is measurable.

## 3. Exact Lean-facing leaf

File:

```text
BanditRLProof/MeasurableLocalQuantities.lean
```

Then import it from:

```lean
BanditRLProof.lean
```

Imports:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import BanditRLProof.MeasurableSums
import BanditRLProof.MathlibWrappers
```

Reason:

`BanditRLProof.MeasurableSums` gives:

```lean
measurable_finset_sum_indicator_reward
```

`BanditRLProof.MathlibWrappers` gives:

```lean
sumRewards_eq_finset_filter_sum
```

`Mathlib.Algebra.BigOperators.Group.Finset.Indicator` gives:

```lean
Finset.sum_indicator_eq_sum_filter
```

which is exactly the bridge between a sum over indicators and a sum over a filtered finset.

Statement:

```lean
theorem measurable_sumRewards
    {Omega : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [AddCommMonoid Reward] [MeasurableAdd₂ Reward]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega => sumRewards (action omega) (reward omega) a n)
```

The suggested proof route is:

1. Get measurability of the `Finset.range n` selected-reward indicator sum from `measurable_finset_sum_indicator_reward`.
2. Prove a pointwise equality from `sumRewards_eq_finset_filter_sum` plus `Finset.sum_indicator_eq_sum_filter`.
3. Rewrite by function extensionality and reuse the finite-sum measurability proof.

## 4. Local APIs to reuse

Reuse exactly:

```lean
measurable_finset_sum_indicator_reward
sumRewards_eq_finset_filter_sum
```

The dependency route should be:

```text
MEAS-FIN-ACTION
  ↓
MEAS-REWARD
  ↓
MEAS-SELECTED-REWARD-FINITE-SUM
  ↓
MEAS-SUMREWARDS
```

Do not unfold `sumRewards`. Do not redo the selected-reward indicator measurability proof. This leaf should only connect the compiled measurable finite-sum theorem to the compiled deterministic `sumRewards` wrapper.

## 5. Mathlib APIs to probe

The key Mathlib theorem is:

```lean
Finset.sum_indicator_eq_sum_filter
```

It has the shape:

```lean
∑ i ∈ s, (t i).indicator (f i) (g i)
  =
∑ i ∈ s with g i ∈ t i, f i (g i)
```

under `[AddCommMonoid β]` and a decidable predicate. That is exactly the identity needed to turn the selected-reward indicator sum into the filtered reward sum.

## 6. Regularity contracts

Use:

```lean
[MeasurableSpace Omega]
[MeasurableSpace Action]
[MeasurableSingletonClass Action]
[MeasurableSpace Reward]
[AddCommMonoid Reward]
[MeasurableAdd₂ Reward]
[DecidableEq Action]
```

plus:

```lean
haction : forall t : Nat, Measurable (fun omega : Omega => action omega t)
hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t)
```

The new `[DecidableEq Action]` is justified here. Unlike the earlier event/indicator lemmas, this theorem connects to `sumRewards_eq_finset_filter_sum`, whose filtered-finset statement uses decidable equality on actions.

Do not add:

```lean
[Fintype Action]
Measure Omega
ProbabilityMeasure Omega
IsProbabilityMeasure μ
Integrable
Rat
Real
Filtration
```

This is still only a measurability theorem.

## 7. Status classification

Classify as:

```text
MEAS-SUMREWARDS: executable local measurable-quantity leaf
```

It should be recorded as a prerequisite for:

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

## 8. Failure policy

Use a fail-closed policy.

If this leaf fails:

1. First check that this import is present:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
```

`Finset.sum_indicator_eq_sum_filter` lives in the finite-indicator big-operator layer, not merely in the basic finite-sum layer.

2. If the pointwise equality is brittle, isolate it as a private helper:

```lean
private theorem sumRewards_eq_finset_range_indicator_reward
    {Omega : Type u} {Action : Type v} {Reward : Type w}
    [DecidableEq Action] [AddCommMonoid Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (a : Action) (n : Nat) (omega : Omega) :
    sumRewards (action omega) (reward omega) a n =
      (Finset.range n).sum
        (fun t : Nat =>
          (({omega' : Omega | action omega' t = a} : Set Omega).indicator
            (fun omega' : Omega => reward omega' t)) omega)
```

Then prove `measurable_sumRewards` by `funext`/`rw` using that helper.

3. Do not replace this with a theorem about only the indicator sum; that already exists.
4. Do not import integration, probability, kernels, filtrations, concentration, or all of Mathlib.
5. Do not specialize to `Rat` or `Real`.

Mark the row complete only after:

```bash
python3 tools\bandit.py check
```

passes.

## 9. Minimal batch before asking again

Complete only:

```text
MEAS-SUMREWARDS
```

with:

```text
BanditRLProof/MeasurableLocalQuantities.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
unfinished/docs/index refresh
python3 tools\bandit.py check
```

Then stop and ask again. The next decision should be between `MEAS-REGRET` and the first expectation canary, depending on whether you want one more measurability bridge before introducing probability measures.
