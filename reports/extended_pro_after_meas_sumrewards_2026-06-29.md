# Extended Pro review after MEAS-SUMREWARDS

I’ll treat this as a next-leaf design review, not a theorem-card review. The key decision is whether to finish measurability of deterministic regret quantities before introducing measures/expectations.

The compiled finite-sum measurability layer now supports a single regret-side bridge, with pseudo-regret measurability looking lower-risk than crossing into expectation.

Thought for 9m 52s

## 1. Review of MEAS-SUMREWARDS

`MEAS-SUMREWARDS` is reasonable as implemented. Do not adjust it before building on it.

The same-universe contract:

```lean
{Action : Type v} {Reward : Type v}
```

is acceptable because it is inherited from the currently compiled deterministic wrapper:

```lean
sumRewards_eq_finset_filter_sum
```

This is a local ABI constraint, not a mathematical problem. Generalizing `sumRewards_eq_finset_filter_sum` to separate universes can be a later cleanup, but it should not block the probability/measurability layer. The private helper was also the right engineering choice: it isolates the pointwise deterministic rewrite from the measurable-function proof.

The import boundary is still acceptable. `Mathlib.MeasureTheory.Group.Arithmetic` is the correct Mathlib layer for measurable additive algebra; it defines `MeasurableAdd₂` and dot-style lemmas such as `Measurable.add`, and it also contains finite-sum measurability APIs generated for `Finset.measurable_sum`.

## 2. Single best next executable leaf

Do `MEAS-REGRET`, implemented narrowly as pseudo-regret random-variable measurability.

Recommended row:

```text
MEAS-REGRET
```

Recommended theorem:

```lean
measurable_pseudoRegret
```

Do not start `EXP-INDICATOR-PULL` or any expectation canary yet. Expectation will force a measure/integration route. Do not start filtration/history/policy yet. The next lowest-risk executable step is to show that the already-defined regret scalar:

```lean
pseudoRegret model (action omega) n
```

is a measurable random variable.

## 3. Exact Lean-facing leaf

File:

```text
BanditRLProof/MeasurableRegret.lean
```

Then import it from:

```lean
BanditRLProof.lean
```

Imports:

```lean
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MathlibWrappers
```

Rationale:

`BanditRLProof.MathlibWrappers` gives:

```lean
pseudoRegret_eq_finset_sum
```

`Mathlib.MeasureTheory.Group.Arithmetic` gives measurable finite sums and additive measurability contracts such as `MeasurableAdd₂` / `Measurable.add`.

`Mathlib.MeasureTheory.MeasurableSpace.Basic`, transitively available through the measure imports, contains `measurable_of_finite`, which proves any function out of a finite measurable-singleton domain is measurable. That is the clean way to show `model.gap` is measurable on `Fin K`.

Statement:

```lean
theorem measurable_pseudoRegret
    {Omega : Type u}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (n : Nat) :
    Measurable
      (fun omega : Omega => pseudoRegret model (action omega) n)
```

Suggested proof route:

1. Prove `hgap : Measurable (fun a : Fin K => model.gap a)` using `measurable_of_finite`.
2. Prove measurability of the finite sum over `Finset.range n` using `Finset.measurable_sum` or finite-set induction.
3. Rewrite by `pseudoRegret_eq_finset_sum`.

## 4. Fallback Proof If Finset.measurable_sum Is Brittle

If Lean has trouble with the generated `Finset.measurable_sum` elaboration, replace only the finite-sum block with induction:

```lean
have hsum :
    Measurable
      (fun omega : Omega =>
        (Finset.range n).sum
          (fun t : Nat => model.gap (action omega t))) := by
  refine Finset.induction_on (Finset.range n) ?h_empty ?h_insert
  · simpa using
      (measurable_const :
        Measurable (fun _ : Omega => (0 : Rat)))
  · intro t s ht ih
    have hterm :
        Measurable
          (fun omega : Omega => model.gap (action omega t)) := by
      exact hgap.comp (haction t)
    simpa [Finset.sum_insert, ht] using hterm.add ih
```

## 5. APIs To Reuse/Probe

Local API:

```lean
pseudoRegret_eq_finset_sum
```

Do not unfold `pseudoRegret`.

Mathlib APIs:

```lean
measurable_of_finite
Measurable.comp
Finset.measurable_sum
```

## 6. Regularity Contracts

Use exactly:

```lean
[MeasurableSpace Omega]
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
[MeasurableSpace Rat]
[MeasurableAdd₂ Rat]
```

plus:

```lean
haction : forall t : Nat,
  Measurable (fun omega : Omega => action omega t)
```

Do not add:

```lean
Measure Omega
ProbabilityMeasure Omega
IsProbabilityMeasure μ
Integrable
Filtration
RewardTrace
TopologicalSpace Rat
BorelSpace Rat
LinearOrder Rat
```

The explicit `[MeasurableSpace Rat] [MeasurableAdd₂ Rat]` contract is intentional. It avoids committing yet to a Borel, discrete, or integration-specific measurable structure on `Rat`.

## 7. Status Classification

Classify this as:

```text
MEAS-REGRET / pseudoRegret random-variable measurability
```

It should close `MEAS-REGRET` only if that row is intended to mean measurability of the local `pseudoRegret` quantity. If the row is broader and meant to include realized regret or reward-dependent regret, record this as a local subleaf:

```text
LOCAL-LEAF-MEASURABLE-REGRET:
- measurable_pseudoRegret
```

and leave the broad row partially open.

## 8. Failure Policy

Use a fail-closed policy.

If this leaf fails:

1. If `measurable_of_finite` cannot synthesize `Finite (Fin K)`, keep the `Mathlib.Data.Fintype.Basic` import and add:

```lean
haveI : Fintype (Fin K) := inferInstance
```

before the `hgap` proof.

2. If needed, replace `measurable_of_finite` with an explicit hypothesis:

```lean
(hgap : Measurable (fun a : Fin K => model.gap a))
```

3. If `Finset.measurable_sum` elaboration fails, use the induction fallback above.
4. If `Rat` measurability or additive measurability is the issue, keep statement-level assumptions:

```lean
[MeasurableSpace Rat] [MeasurableAdd₂ Rat]
```

5. Do not import Borel/Real/integration just to solve this leaf.
6. Do not add probability measures, expectations, filtrations, kernels, concentration, or all of Mathlib.
7. Do not prove this by recursion over `pseudoRegret`; consume `pseudoRegret_eq_finset_sum`.

Mark the row complete only after:

```bash
python3 tools\bandit.py check
```

passes.

## 9. Minimal Batch Before Asking Again

Complete only:

```text
MEAS-REGRET
```

with:

```text
BanditRLProof/MeasurableRegret.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
unfinished/docs/index refresh
python3 tools\bandit.py check
```

Then stop. The next review should decide whether to introduce the first expectation canary or add a measurable pull-count bridge before expectation.
