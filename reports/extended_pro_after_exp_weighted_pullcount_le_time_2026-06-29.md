# Extended Pro Review: After EXP-WEIGHTED-PULLCOUNT-LE-TIME

Extended Pro accepted `EXP-WEIGHTED-PULLCOUNT-LE-TIME` as the correct generic
`ENNReal` probability bridge.  It advised not to revise it before building on
it.

Recommended next single executable leaf:

```text
EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN
```

Recommended theorem:

```lean
theorem lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (gap : Fin K -> ENNReal) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            gap a *
              ((pullCount (action omega) a n : Nat) : ENNReal)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        gap a * (n : ENNReal))
```

Recommended file:

```text
BanditRLProof/ExpectationFiniteBanditBounds.lean
```

Recommended imports:

```lean
import Mathlib.Data.Fintype.Basic
import BanditRLProof.ExpectationWeightedPullCountBounds
```

Failure policy:

- If `Finset.univ` or `Fintype (Fin K)` fails, keep
  `Mathlib.Data.Fintype.Basic` and add `haveI : Fintype (Fin K) :=
  inferInstance`.
- If `DecidableEq (Fin K)` does not synthesize, add `haveI : DecidableEq
  (Fin K) := inferInstance`.
- If the one-line proof does not close, make `(Action := Fin K)` and
  `(arms := (Finset.univ : Finset (Fin K)))` explicit.
- Do not introduce `FiniteBanditModel K`, `Rat`, `Real`, Bochner integration,
  kernels, filtrations, or concentration.
- Mark complete only after `python3 tools/bandit.py check` passes.

Minimal batch:

- `BanditRLProof/ExpectationFiniteBanditBounds.lean`;
- root import in `BanditRLProof.lean`;
- one consumer test in `Tests/Basic.lean`;
- unfinished/docs/index refresh;
- `python3 tools/bandit.py check`;
- then ask again before scalar conversion for `FiniteBanditModel.gap : Fin K
  -> Rat`.
