# Extended Pro Review Prompt: After EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG

We are working in the Lean 4 repository `Auto-Bandit-RL-Proof-In-Sleep`.

Following your previous recommendation, I completed exactly one leaf:

```text
EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG
```

New compiled file:

```text
BanditRLProof/ExpectationPseudoRegretRatBounds.lean
```

New theorem:

```lean
theorem BanditRLProof.lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hgap : forall a : Fin K,
      (0 : Rat) <= model.gap a)
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

Implementation notes:

- The file imports:

  ```lean
  import Mathlib.Data.Rat.Cast.Order
  import BanditRLProof.ExpectationPseudoRegretOfRealBounds
  ```

- The proof calls:

  ```lean
  lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg
  ```

  and uses:

  ```lean
  (Rat.cast_nonneg (K := Real)).mpr
  ```

  to convert `(0 : Rat) <= model.gap a` into
  `0 <= (((model.gap a : Rat) : Real))`.

Verification passed:

```text
python3 tools/bandit.py check
Build completed successfully (1775 jobs).
Build completed successfully (1777 jobs).
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
EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG
```

Important boundary:

- This is still an `ENNReal.ofReal` lower-integral theorem.
- It is not Rat-valued expected regret.
- It is not Bochner expected regret.
- It assumes Rat-level gap nonnegativity; it does not prove
  `FiniteBanditModel.gap` nonnegative from the model internals.
- It does not introduce integrability, filtrations, kernels, conditional
  expectation, concentration, or algorithm-specific final theorem work.

Please review this completed adapter and recommend the next single executable
Lean leaf.

Questions:

1. Is `EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` reasonable as
   implemented and correctly classified as a Rat-contract adapter only?
2. Does the current local `FiniteBanditModel.bestArm` API support proving
   `theorem FiniteBanditModel.gap_nonneg`, or should the next leaf first prove
   a best-arm dominance invariant?
3. Please give exactly one next executable leaf, with:
   - exact Lean-facing statement;
   - local APIs/imports;
   - intended proof route;
   - regularity contracts;
   - retrieval evidence from Mathlib/local declarations;
   - status classification;
   - failure policy.
4. How much should be completed before I ask you again?
