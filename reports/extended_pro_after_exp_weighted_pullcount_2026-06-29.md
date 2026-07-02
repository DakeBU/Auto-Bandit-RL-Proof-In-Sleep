# Extended Pro Review: After EXP-WEIGHTED-PULLCOUNT-LINTEGRAL

Extended Pro accepted `EXP-WEIGHTED-PULLCOUNT-LINTEGRAL` as the right stopping
point before Bochner expectation, integrability, filtrations, kernels, or
concentration.  It classified the theorem as a reusable `ENNReal` lower-
integral bridge, not as full `EXP-REGRET-PULLCOUNT`.

Recommended next single executable leaf:

```text
EXP-PULLCOUNT-LE-TIME
```

Recommended theorem:

```lean
theorem lintegral_natCast_pullCount_le_time
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount (action omega) a n : Nat) : ENNReal))
      <= (n : ENNReal)
```

Recommended file:

```text
BanditRLProof/ExpectationPullCountBounds.lean
```

Recommended imports:

```lean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import BanditRLProof.ExpectationPullCount
```

Proof route:

1. Rewrite the lower integral with
   `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq`.
2. Bound every event measure by `1` using `MeasureTheory.prob_le_one`.
3. Sum the pointwise inequalities with `Finset.sum_le_sum`.
4. Simplify the constant-one sum over `Finset.range n` to `(n : ENNReal)`.

Failure policy:

- If `prob_le_one` is unavailable, check
  `Mathlib.MeasureTheory.Measure.Typeclasses.Probability`.
- If typeclass synthesis fails for `prob_le_one`, try
  `[MeasureTheory.IsZeroOrProbabilityMeasure mu]` instead of
  `[MeasureTheory.IsProbabilityMeasure mu]`.
- If `Finset.sum_le_sum` is unavailable, keep/add
  `Mathlib.Algebra.Order.BigOperators.Group.Finset`.
- Do not import Bochner integration, conditional expectation, filtrations,
  kernels, concentration, or all of Mathlib.
- Do not specialize to `Fin K`, `Rat`, or `Real`.
- Mark complete only after `python3 tools/bandit.py check` passes.

Minimal batch:

- `BanditRLProof/ExpectationPullCountBounds.lean`;
- root import in `BanditRLProof.lean`;
- one consumer test in `Tests/Basic.lean`;
- unfinished/docs/index refresh;
- `python3 tools/bandit.py check`;
- then ask Extended Pro again before choosing a weighted probability bound or
  Bochner expected-regret route.
