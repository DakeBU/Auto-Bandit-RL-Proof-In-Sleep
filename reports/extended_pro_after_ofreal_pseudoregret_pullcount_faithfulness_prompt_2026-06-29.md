# Extended Pro Review Prompt: After OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS

We are working in the Lean 4 repository `Auto-Bandit-RL-Proof-In-Sleep`.

Following your previous recommendation, I completed exactly one leaf:

```text
OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS
```

New compiled file:

```text
BanditRLProof/ScalarPseudoRegret.lean
```

New public theorem:

```lean
theorem BanditRLProof.ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (hgap : forall a : Fin K,
      0 <= (((model.gap a : Rat) : Real)))
    (n : Nat) :
    ENNReal.ofReal (((pseudoRegret model action n : Rat) : Real))
      =
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          ((pullCount action a n : Nat) : ENNReal))
```

Implementation notes:

- The file imports:

  ```lean
  import Mathlib.Algebra.Field.Rat
  import Mathlib.Data.Rat.BigOperators
  import Mathlib.Data.Fintype.Basic
  import BanditRLProof.ScalarENNReal
  import BanditRLProof.RegretDecomposition
  ```

- I used a private helper to cast the deterministic Rat-valued regret
  decomposition into Real:

  ```lean
  private theorem real_pseudoRegret_eq_univ_sum_model_gap_mul_natCast_pullCount
  ```

- The helper needed `Mathlib.Data.Rat.BigOperators` so `Rat.cast_sum` is
  available to `simp`.
- The main theorem then rewrites `pseudoRegret` via that helper and applies:

  ```lean
  BanditRLProof.ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg
  ```

Verification passed:

```text
lake build BanditRLProof.ScalarPseudoRegret
Build completed successfully.

lake build Tests.Basic
Build completed successfully.

python3 tools/bandit.py check
Build completed successfully (1773 jobs).
Build completed successfully (1775 jobs).
check passed
```

I also updated:

- root import in `BanditRLProof.lean`;
- one consumer test in `Tests/Basic.lean`;
- `tools/bandit.py` local leaf cards and `unfinished` recommendation output;
- `research-wiki/theory-tree/mathlib-foundation-leaf-map.md`;
- `docs/completion_gap_audit.md`;
- `docs/project_overview_next_plan.md`;
- `docs/collaborator_unfinished_work_guide.md`;
- `README.md`;
- `research-wiki/theory-tree/bandit-theory-tree.md`;
- UCB/ETC proof-obligation ledgers;
- retrieval indexes via `python3 tools/bandit.py reference-index`;
- UCB/ETC memory-refresh artifacts.

Important boundary:

- I have not claimed expected regret.
- I have not proved `FiniteBanditModel.gap` nonnegative from model internals.
- I have not lifted the pointwise theorem into `lintegral`.
- I have not introduced Bochner expectation, integrability, filtrations,
  kernels, conditional expectation, concentration, or algorithm-specific final
  theorem work.

Current compiled bridge chain now includes:

```text
EXP-MODEL-GAP-OFREAL-BOUND
OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS
OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS
```

Please review whether this latest pointwise scalar/model leaf is correct and
recommend the next single executable Lean leaf.

Questions:

1. Is `OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS` reasonable as implemented
   and correctly classified as pointwise scalar/model algebra only?
2. Should the next leaf lift this pointwise theorem into the existing
   `lintegral` model-gap bound, prove `FiniteBanditModel.gap` nonnegativity
   from the model definition, or move to an integrability/Bochner design leaf?
3. Please give exactly one next executable leaf, with:
   - exact Lean-facing statement;
   - local APIs/imports;
   - intended proof route;
   - regularity contracts;
   - retrieval evidence from Mathlib/local declarations;
   - status classification;
   - failure policy.
4. How much should be completed before I ask you again?
