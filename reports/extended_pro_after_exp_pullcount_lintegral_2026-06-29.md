# Extended Pro review after EXP-PULLCOUNT-LINTEGRAL

Extended Pro accepted `EXP-PULLCOUNT-LINTEGRAL /
lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq` and
recommended one next executable leaf, but I did not implement it in this batch.

## Review

`EXP-PULLCOUNT-LINTEGRAL /
lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq` is reasonable
as implemented. Do not adjust it before building on it.

The accepted dependency chain is:

```text
EXP-INDICATOR-PULL
  -> EXP-FINSET-INDICATOR-PULL
  -> EXP-PULLCOUNT-LINTEGRAL
```

The private pointwise helper is acceptable because it only connects recursive
`pullCount` to the finite sum of action-event indicators. Staying in
`ENNReal / lintegral` was also the correct choice.

## Next Leaf

Recommended local row:

```text
EXP-WEIGHTED-PULLCOUNT-LINTEGRAL
```

Recommended theorem:

```lean
lintegral_finset_sum_gap_mul_natCast_pullCount_eq
```

Target shape:

```lean
MeasureTheory.lintegral mu
  (fun omega =>
    arms.sum
      (fun a =>
        gap a * ((pullCount (action omega) a n : Nat) : ENNReal)))
  =
arms.sum
  (fun a =>
    gap a *
      (Finset.range n).sum
        (fun t => mu {omega | action omega t = a}))
```

Use arbitrary:

```lean
gap : Action -> ENNReal
arms : Finset Action
```

Do not specialize to `Fin K`, `FiniteBanditModel`, `Rat`, or `Real`. Do not
move to Bochner expectation, filtrations, kernels, concentration, or algorithm
theorems yet.

## Recommended File

```text
BanditRLProof/ExpectationWeightedPullCount.lean
```

Root import:

```lean
import BanditRLProof.ExpectationWeightedPullCount
```

## Recommended Imports

```lean
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.ExpectationPullCount
import BanditRLProof.MeasurablePullCountCast
```

## APIs To Reuse

Local APIs:

```lean
measurable_natCast_pullCount
lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq
```

Mathlib APIs:

```lean
MeasureTheory.lintegral_finset_sum
MeasureTheory.lintegral_const_mul
Measurable.const_mul
```

Use `MeasureTheory.lintegral_finset_sum` for this pinned Mathlib version,
because that API already compiled locally.

## Contracts

Use:

```lean
[MeasurableSpace Omega]
[MeasurableSpace Action]
[MeasurableSingletonClass Action]
[DecidableEq Action]
(mu : Measure Omega)
haction : forall t : Nat,
  Measurable (fun omega : Omega => action omega t)
gap : Action -> ENNReal
arms : Finset Action
```

Do not add:

```lean
[Fintype Action]
ProbabilityMeasure Omega
IsProbabilityMeasure mu
Integrable
Real
Rat
FiniteBanditModel
Filtration
Kernel
```

## Status Classification

Classify as:

```text
EXP-WEIGHTED-PULLCOUNT-LINTEGRAL: executable lower-integral weighted-count bridge
```

It is a prerequisite for `EXP-REGRET-PULLCOUNT`, UCB/ETC expected-regret
scaffolding, and nonnegative regret upper-bound routes. It should not close the
full `EXP-REGRET-PULLCOUNT` theorem card unless that row is explicitly narrowed
to an `ENNReal` nonnegative weighted-count identity.

## Failure Policy

If the theorem fails:

- keep it over arbitrary `gap : Action -> ENNReal` and `arms : Finset Action`;
- do not specialize to `Fin K`;
- switch between `MeasureTheory.lintegral_finset_sum` and
  `MeasureTheory.lintegral_finsetSum` depending on local Mathlib;
- if measurability fails, try the explicit `Measurable.const_mul` form;
- if constant multiplication under `lintegral` fails, inspect the argument
  order of `MeasureTheory.lintegral_const_mul` before changing the theorem.

Do not import Bochner integration, conditional expectation, filtrations,
kernels, concentration, or all of Mathlib.

## Minimal Batch

Complete only:

```text
EXP-WEIGHTED-PULLCOUNT-LINTEGRAL
```

with:

```text
BanditRLProof/ExpectationWeightedPullCount.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
unfinished/docs/index refresh
python3 tools\bandit.py check
```

Then ask again. The next review should decide whether to specialize this to
`Fin K / Finset.univ` or begin the separate `Rat / Real` Bochner expectation
design.
