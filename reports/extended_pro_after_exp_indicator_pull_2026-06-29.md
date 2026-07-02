# Extended Pro review after EXP-INDICATOR-PULL

Extended Pro accepted `EXP-INDICATOR-PULL /
lintegral_actionTrace_eval_eq_indicator_one` and recommended one more
`ENNReal` lower-integral bridge before connecting the result to `pullCount`.

## Review of EXP-INDICATOR-PULL

`EXP-INDICATOR-PULL / lintegral_actionTrace_eval_eq_indicator_one` is
reasonable as implemented. Do not adjust it before building on it.

The implementation made the right choices:

- arbitrary measure through `(mu : Measure Omega)`;
- `ENNReal` lower integral, not Bochner expectation;
- event measurability reused through `measurableSet_actionTrace_eval_eq`;
- robust explicit statement using `MeasureTheory.lintegral`;
- non-eta-expanded indicator form `s.indicator (1 : Omega -> ENNReal)`.

Using `MeasureTheory.lintegral_indicator_one` was appropriate because the local
Mathlib version exposes that theorem, while the eta-expanded
`lintegral_indicator_fun_one` route was not available locally.

## Next Leaf

Do an `ENNReal` finite-sum indicator expectation bridge next.

Recommended local row:

```text
EXP-FINSET-INDICATOR-PULL
```

Recommended theorem:

```lean
lintegral_finset_sum_actionTrace_eval_eq_indicator_one
```

This should be the next step before the measure-theoretic pull-count identity.
It tests finite-sum lower-integral interchange without adding `pullCount`, Nat
casts, expected regret, `Rat`, `Real`, Bochner expectation, histories,
policies, filtrations, kernels, or concentration.

## Recommended File

```text
BanditRLProof/ExpectationSums.lean
```

Root import:

```lean
import BanditRLProof.ExpectationSums
```

## Recommended Imports

```lean
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import BanditRLProof.ExpectationFoundation
```

## Recommended Statement

```lean
theorem lintegral_finset_sum_actionTrace_eval_eq_indicator_one
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (mu : Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (s : Finset Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        s.sum
          (fun t : Nat =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (1 : Omega -> ENNReal)) omega))
      =
    s.sum
      (fun t : Nat =>
        mu {omega : Omega | action omega t = a})
```

## Proof Route

Use:

```lean
measurable_actionTrace_eval_eq_indicator_const
lintegral_actionTrace_eval_eq_indicator_one
MeasureTheory.lintegral_finsetSum
```

Fallback Mathlib API:

```lean
MeasureTheory.lintegral_finset_sum
```

Do not reprove event measurability. Do not unfold `ActionTrace`.

## Contracts

Use exactly:

```lean
[MeasurableSpace Omega]
[MeasurableSpace Action]
[MeasurableSingletonClass Action]
(mu : Measure Omega)
haction : forall t : Nat,
  Measurable (fun omega : Omega => action omega t)
```

Do not add:

```lean
[DecidableEq Action]
[Fintype Action]
ProbabilityMeasure Omega
IsProbabilityMeasure mu
Integrable
Rat
Real
Filtration
Kernel
```

No decidable equality is needed because the theorem remains in `Set.indicator`
form.

## Status Classification

Classify this as:

```text
EXP-FINSET-INDICATOR-PULL: executable lower-integral finite-sum bridge
```

It should be recorded as a prerequisite for:

```text
measure-theoretic pull-count identity
EXP-REGRET-PULLCOUNT
UCB/ETC expected count bounds
```

It should not close:

```text
EXP-REGRET-PULLCOUNT
COND-EXPECT-REWARD
FILTRATION-HISTORY
ADAPTED-ACTION
MART-DIFF-REWARD
```

This is still `ENNReal` lower-integral algebra, not Bochner expectation or
conditional expectation.

## Failure Policy

Use a fail-closed policy.

If this leaf fails:

- first confirm the import
  `Mathlib.MeasureTheory.Integral.Lebesgue.Add`;
- if `lintegral_finsetSum` does not exist locally, try
  `MeasureTheory.lintegral_finset_sum`;
- keep the non-eta-expanded `(1 : Omega -> ENNReal)` form if elaboration is
  brittle;
- if the measurability block fails, use the direct proof
  `Measurable.indicator measurable_const
  (measurableSet_actionTrace_eval_eq action haction a t)`.

Do not switch to Bochner expectation, `Real`, `Rat`, conditional expectation,
probability-measure classes, kernels, filtrations, concentration, or all of
Mathlib. Do not replace this with the pull-count identity in the same batch.

## Minimal Batch

Complete only:

```text
EXP-FINSET-INDICATOR-PULL
```

with:

```text
BanditRLProof/ExpectationSums.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
unfinished/docs/index refresh
python3 tools\bandit.py check
```

Then stop. The next review should decide whether to connect this theorem to
`pullCount` through an `ENNReal` measure-theoretic pull-count identity.
