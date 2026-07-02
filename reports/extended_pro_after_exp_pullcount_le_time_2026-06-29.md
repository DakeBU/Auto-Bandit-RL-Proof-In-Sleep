# Extended Pro Review: After EXP-PULLCOUNT-LE-TIME

Extended Pro accepted `EXP-PULLCOUNT-LE-TIME` /
`lintegral_natCast_pullCount_le_time` as the right first probability-measure
corollary after the lower-integral pull-count identity.  It advised not to
revise that theorem before building on it.

Recommended next single executable leaf:

```text
EXP-WEIGHTED-PULLCOUNT-LE-TIME
```

Recommended theorem:

```lean
theorem lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (gap : Action -> ENNReal) (arms : Finset Action) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        arms.sum
          (fun a : Action =>
            gap a *
              ((pullCount (action omega) a n : Nat) : ENNReal)))
      <=
    arms.sum
      (fun a : Action =>
        gap a * (n : ENNReal))
```

Recommended file:

```text
BanditRLProof/ExpectationWeightedPullCountBounds.lean
```

Recommended imports:

```lean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import BanditRLProof.ExpectationWeightedPullCount
import BanditRLProof.ExpectationPullCountBounds
```

Proof route:

1. Rewrite with `lintegral_finset_sum_gap_mul_natCast_pullCount_eq`.
2. Apply `Finset.sum_le_sum`.
3. Reuse `lintegral_natCast_pullCount_le_time` for each arm.
4. Multiply the pointwise pull-count bound by `gap a` in `ENNReal`.

Failure policy:

- If multiplication monotonicity fails with `mul_le_mul`, try
  `mul_le_mul_left' hcount (gap a)`.
- If the local equality rewrite is brittle, prove the per-arm count bound
  directly with `prob_le_one`, `Finset.sum_le_sum`, and `simp`.
- Do not import Bochner integration, conditional expectation, filtrations,
  kernels, concentration, or all of Mathlib.
- Do not specialize to `Fin K`, `Rat`, or `Real`.
- Mark complete only after `python3 tools/bandit.py check` passes.

Minimal batch:

- `BanditRLProof/ExpectationWeightedPullCountBounds.lean`;
- root import in `BanditRLProof.lean`;
- one consumer test in `Tests/Basic.lean`;
- unfinished/docs/index refresh;
- `python3 tools/bandit.py check`;
- then ask again before choosing a `Fin K`/`Finset.univ` specialization or the
  separate scalar-design step for `Rat`/`Real` expected regret.
