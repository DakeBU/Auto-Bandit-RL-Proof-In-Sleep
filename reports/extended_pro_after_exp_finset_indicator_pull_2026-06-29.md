# Extended Pro review after EXP-FINSET-INDICATOR-PULL

Extended Pro accepted `EXP-FINSET-INDICATOR-PULL /
lintegral_finset_sum_actionTrace_eval_eq_indicator_one` and recommended one
connector back to the local recursive `pullCount`, still staying in `ENNReal`
and `lintegral`.

## Review

`EXP-FINSET-INDICATOR-PULL /
lintegral_finset_sum_actionTrace_eval_eq_indicator_one` is reasonable as
implemented. Do not adjust it before building on it.

The accepted choices were:

- arbitrary measure, not probability-specific;
- `ENNReal` lower integral, not Bochner expectation;
- arbitrary `s : Finset Nat`;
- non-eta-expanded indicator `(1 : Omega -> ENNReal)`;
- local use of `MeasureTheory.lintegral_finset_sum`, matching the pinned
  Mathlib API.

## Next Leaf

Recommended local row:

```text
EXP-PULLCOUNT-LINTEGRAL
```

Recommended theorem:

```lean
lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq
```

Target identity:

```lean
∫⁻ omega, N_a(n, omega) ∂mu
  =
∑ t in range n, mu {omega | A_t omega = a}
```

with `N_a(n, omega)` represented as
`((pullCount (action omega) a n : Nat) : ENNReal)`.

Do not move to `MEAS-HISTORY`, `MEAS-POLICY`, Bochner expectation, expected
regret, kernels, filtrations, or concentration yet.

## Recommended File

```text
BanditRLProof/ExpectationPullCount.lean
```

Root import:

```lean
import BanditRLProof.ExpectationPullCount
```

## Recommended Imports

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Cast.Basic
import BanditRLProof.ExpectationSums
import BanditRLProof.LeafLemmas
```

## Proof Route

Add a private pointwise helper:

```lean
private theorem ennreal_natCast_pullCount_eq_finset_range_indicator_one
    {Omega : Type u} {Action : Type v} [DecidableEq Action]
    (action : Omega -> ActionTrace Action) (a : Action) (n : Nat)
    (omega : Omega) :
    ((pullCount (action omega) a n : Nat) : ENNReal) =
      (Finset.range n).sum
        (fun t : Nat =>
          (({omega' : Omega | action omega' t = a} : Set Omega).indicator
            (1 : Omega -> ENNReal)) omega)
```

Then rewrite the integrand with that helper and apply:

```lean
lintegral_finset_sum_actionTrace_eval_eq_indicator_one
```

Use `pullCount_succ`, `Finset.sum_range_succ`, and `Nat.cast_add` in the
pointwise helper. Do not unfold the measure/integral proof again.

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
```

Do not add:

```lean
[Fintype Action]
ProbabilityMeasure Omega
IsProbabilityMeasure mu
Integrable
Real
Rat
Filtration
Kernel
```

## Failure Policy

If the recursive helper fails:

- inspect `pullCount_succ`;
- add `Nat.succ_eq_add_one` to the local `simp` set if needed;
- use `Finset.sum_range_succ` explicitly if the successor sum does not
  simplify;
- add `Nat.cast_add` to the local `simp` set if Nat-cast normalization fails;
- only as fallback, use `pullCount_eq_finset_filter_card` and
  `Finset.sum_indicator_eq_sum_filter`.

Do not switch to Bochner expectation, `Real`, `Rat`, conditional expectation,
probability-measure classes, kernels, filtrations, concentration, or all of
Mathlib.

## Minimal Batch

Complete only:

```text
EXP-PULLCOUNT-LINTEGRAL
```

with:

```text
BanditRLProof/ExpectationPullCount.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
unfinished/docs/index refresh
python3 tools\bandit.py check
```

Then ask again. The next review should decide whether to introduce a
constrained expected-regret bridge or add one more `ENNReal` count-sum
corollary.
