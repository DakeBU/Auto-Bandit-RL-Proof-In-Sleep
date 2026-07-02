# Extended Pro review after MEAS-PULLCOUNT-CAST

Extended Pro accepted `MEAS-PULLCOUNT-CAST / measurable_natCast_pullCount`
and recommended entering the expectation/integration layer with exactly one
minimal `ENNReal` lower-integral canary.

## Review of MEAS-PULLCOUNT-CAST

`MEAS-PULLCOUNT-CAST / measurable_natCast_pullCount` is reasonable as
implemented. Do not adjust it before building on it.

The direct scalar induction was the right proof route. It avoids adding a
measurable-space contract on `Nat`, and it produces the scalar-valued form
needed by the compiled regret decomposition:

```lean
model.gap a * (pullCount action a t : Rat)
```

The generic scalar contract is appropriate:

```lean
[MeasurableSpace Beta] [AddCommMonoidWithOne Beta] [MeasurableAdd₂ Beta]
```

This keeps the theorem reusable for `Rat`, `Real`, or another additive scalar
later. The proof's reliance on `Measurable.ite`, `Measurable.add`, and
`pullCount_succ` is cleaner than routing through filtered `Finset.card`.

## Next Leaf

Start the first expectation/integration canary now, but keep it minimal.

Recommended row:

```text
EXP-INDICATOR-PULL
```

Recommended implementation:

```text
EXP-INDICATOR-PULL / lintegral indicator-one equals event measure
```

This should be an `ENNReal` lower-Lebesgue-integral statement:

```lean
∫⁻ omega, 1{A_t = a}(omega) ∂mu = mu {omega | A_t omega = a}
```

Do not start `EXP-REGRET-PULLCOUNT`, Bochner expectation, conditional
expectation, filtrations, kernels, or concentration yet. This leaf is the
smallest honest import of measure/integral machinery.

## Recommended File

```text
BanditRLProof/ExpectationFoundation.lean
```

Root import:

```lean
import BanditRLProof.ExpectationFoundation
```

## Recommended Imports

```lean
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import BanditRLProof.MeasureFoundation
```

Use:

```lean
open MeasureTheory
open scoped ENNReal
```

## Recommended Statement

```lean
theorem lintegral_actionTrace_eval_eq_indicator_one
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (mu : Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) :
    (∫⁻ omega : Omega,
      (({omega' : Omega | action omega' t = a} : Set Omega).indicator
        (fun _ : Omega => (1 : ENNReal))) omega ∂mu)
      =
    mu {omega : Omega | action omega t = a}
```

Alternative theorem name:

```lean
lintegral_pull_indicator_eq_measure_actionTrace_eval_eq
```

## Proof Route

Reuse exactly:

```lean
measurableSet_actionTrace_eval_eq
```

Primary Mathlib API:

```lean
MeasureTheory.lintegral_indicator_fun_one
```

Fallback API:

```lean
MeasureTheory.lintegral_indicator_one
```

Do not use `measurable_actionTrace_eval_eq_indicator_const`,
`measurable_pullCount`, or `measurable_natCast_pullCount` for this proof.
Those remain downstream prerequisites, but the lower-integral indicator-one
identity only needs the measurable event set.

## Contracts

Use exactly:

```lean
[MeasurableSpace Omega]
[MeasurableSpace Action]
[MeasurableSingletonClass Action]
(mu : Measure Omega)
```

plus:

```lean
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
Real
Rat
Filtration
```

The theorem is valid for an arbitrary measure. If `mu` is later a probability
measure, then `mu {omega | action omega t = a}` is the event probability, but
this leaf should not require that assumption.

## Status Classification

Classify this as:

```text
EXP-INDICATOR-PULL: executable lower-integral canary
```

or, if the project wants to reserve `EXP-*` for Bochner expectation only:

```text
LOCAL-LEAF-EXP-INDICATOR-PULL-LINTEGRAL
```

Extended Pro recommends allowing it to close `EXP-INDICATOR-PULL` if that row's
intended meaning is the basic identity "expected indicator equals event
measure/probability."

It should not close:

```text
EXP-REGRET-PULLCOUNT
COND-EXPECT-REWARD
MART-DIFF-REWARD
```

This is an `ENNReal` lower-integral identity, not a Bochner expectation or
conditional-expectation theorem.

## Failure Policy

Use a fail-closed policy.

If this leaf fails:

- first confirm the import
  `Mathlib.MeasureTheory.Integral.Lebesgue.Basic`;
- if notation fails, keep `open MeasureTheory` and `open scoped ENNReal`;
- if `lintegral_indicator_fun_one` does not elaborate, try
  `MeasureTheory.lintegral_indicator_one`;
- if the eta-expanded `fun _ => (1 : ENNReal)` form is brittle, state the
  theorem with `s.indicator 1` instead.

Do not switch to Bochner expectation, `Real`, `Rat`, conditional expectation,
probability-measure classes, kernels, filtrations, or concentration. Do not
import all of Mathlib.

Mark the row complete only after:

```bash
python3 tools\bandit.py check
```

passes.

## Minimal Batch

Complete only:

```text
EXP-INDICATOR-PULL
```

with:

```text
BanditRLProof/ExpectationFoundation.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
unfinished/docs/index refresh
python3 tools\bandit.py check
```

Then ask again. The next review should decide between an `ENNReal` finite-sum
expectation bridge and a measure-theoretic pull-count identity, not expected
regret yet.
