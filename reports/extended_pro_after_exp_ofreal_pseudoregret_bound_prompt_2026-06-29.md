# Extended Pro Review Prompt: After EXP-OFREAL-PSEUDOREGRET-BOUND

We are working in the Lean 4 repository `Auto-Bandit-RL-Proof-In-Sleep`.

Following your previous recommendation, I completed exactly one leaf:

```text
EXP-OFREAL-PSEUDOREGRET-BOUND
```

New compiled file:

```text
BanditRLProof/ExpectationPseudoRegretOfRealBounds.lean
```

New theorem:

```lean
theorem BanditRLProof.lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hgap : forall a : Fin K,
      0 <= (((model.gap a : Rat) : Real)))
    (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model (action omega) n : Rat) : Real)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          (n : ENNReal))
```

The proof uses exactly:

```lean
BanditRLProof.ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg
lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time
```

It applies `MeasureTheory.lintegral_congr` to rewrite the integrand pointwise,
then applies the existing model-gap lower-integral bound.

Verification passed:

```text
lake build BanditRLProof.ExpectationPseudoRegretOfRealBounds
Build completed successfully.

lake build Tests.Basic
Build completed successfully.

python3 tools/bandit.py check
Build completed successfully (1774 jobs).
Build completed successfully (1776 jobs).
check passed
```

I also updated:

- root import in `BanditRLProof.lean`;
- one consumer test in `Tests/Basic.lean`;
- `tools/bandit.py` local leaf cards and unfinished recommendation output;
- `research-wiki/theory-tree/mathlib-foundation-leaf-map.md`;
- `docs/completion_gap_audit.md`;
- `docs/project_overview_next_plan.md`;
- `docs/collaborator_unfinished_work_guide.md`;
- `README.md`;
- `research-wiki/theory-tree/bandit-theory-tree.md`;
- UCB/ETC proof-obligation ledgers;
- retrieval indexes and UCB/ETC memory-refresh artifacts.

Current compiled chain now includes:

```text
EXP-MODEL-GAP-OFREAL-BOUND
OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS
OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS
EXP-OFREAL-PSEUDOREGRET-BOUND
```

Important boundary:

- This is still an `ENNReal.ofReal` lower-integral theorem.
- It is not Rat-valued expected regret.
- It is not Bochner expected regret.
- It does not prove `FiniteBanditModel.gap` nonnegative from the model
  internals.
- It does not introduce integrability, filtrations, kernels, conditional
  expectation, concentration, or algorithm-specific final theorem work.

Please review this completed leaf and recommend the next single executable
Lean leaf.

Questions:

1. Is `EXP-OFREAL-PSEUDOREGRET-BOUND` reasonable as implemented and correctly
   classified as an `ENNReal.ofReal` lower-integral bound only?
2. Should the next leaf prove model-gap nonnegativity from
   `FiniteBanditModel.bestArm`, begin a separate Bochner/integrability route,
   or do another narrow `ENNReal` bridge first?
3. Please give exactly one next executable leaf, with:
   - exact Lean-facing statement;
   - local APIs/imports;
   - intended proof route;
   - regularity contracts;
   - retrieval evidence from Mathlib/local declarations;
   - status classification;
   - failure policy.
4. How much should be completed before I ask you again?
