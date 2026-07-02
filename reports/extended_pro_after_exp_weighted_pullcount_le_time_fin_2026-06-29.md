# Extended Pro Review: After EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN

Extended Pro accepted `EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN` as the right final
specialization of the current `ENNReal` / `lintegral` probability bridge
before scalar-conversion work.

Recommended next single executable leaf:

```text
EXP-MODEL-GAP-OFREAL-BOUND
```

Recommended theorem:

```lean
theorem lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            ENNReal.ofReal (((model.gap a : Rat) : Real)) *
              ((pullCount (action omega) a n : Nat) : ENNReal)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) * (n : ENNReal))
```

Recommended file:

```text
BanditRLProof/ExpectationFiniteBanditModelBounds.lean
```

Recommended imports:

```lean
import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Field.Rat
import BanditRLProof.ExpectationFiniteBanditBounds
```

Important classification:

- This is an `ENNReal.ofReal` surrogate bound for model gaps.
- It is not full `EXP-REGRET-PULLCOUNT`.
- `ENNReal.ofReal` clamps negative real inputs to zero, so a later
  faithfulness bridge must either prove `FiniteBanditModel.gap` is nonnegative
  or add an explicit nonnegativity contract before claiming equality with
  Rat-valued pseudo-regret.

Failure policy:

- Keep `Mathlib.Data.ENNReal.Real` for `ENNReal.ofReal`.
- Keep `Mathlib.Algebra.Field.Rat` for the explicit Rat-to-Real cast.
- If the one-line `simpa` fails, introduce a local abbreviation
  `gapENN : Fin K -> ENNReal`.
- Do not switch to Bochner expectation, `Integrable`, conditional expectation,
  filtrations, kernels, concentration, or broad imports.
- Do not claim this proves expected regret for Rat-valued `pseudoRegret`.

Minimal batch:

- `BanditRLProof/ExpectationFiniteBanditModelBounds.lean`;
- root import in `BanditRLProof.lean`;
- one consumer test in `Tests/Basic.lean`;
- unfinished/docs/index refresh;
- `python3 tools/bandit.py check`;
- then stop and review the faithfulness bridge.
