# Extended Pro Review Response: After Oracle Filtered-Sum Probability Wrapper

- Prompt: `reports/extended_pro_after_commit_oracle_filtered_candidate_prompt_2026-06-30.md`
- URL: `https://chatgpt.com/c/6a4317fa-d1ac-83e8-8461-feea0c7f68f3`
- Boundary: `ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL`
- Chosen next leaf: `ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL`
- Extraction note: raw assistant response extracted from the ChatGPT message DOM after completion.

## Raw Extended Pro Response

Review of completed leaf

`ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail` is reasonable and well-scoped.

It is a valid saturation step because it:

- specializes an already compiled arbitrary commit-arm probability consumer;
- uses `commitArm omega := oracle.choose (empMean omega)`;
- exposes the oracle-facing wrong-commit event directly;
- preserves the filtered nonbest-arm RHS;
- does not require oracle measurability;
- does not construct a concrete argmax oracle;
- does not introduce concentration, filtration, conditional expectation, or final ETC regret.

So the completed leaf is coherent with the current project strategy.

Selected next leaf

Choose Candidate A:

`ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL`

This is the right next step because it completes the oracle-specialized probability-wrapper family by adding the sibling if-zeroed version:

```lean
(Finset.univ : Finset (Fin K)).sum
  (fun a : Fin K => if a = model.bestArm then 0 else tail a)
```

The filtered statement is mathematically cleaner, but the if-zeroed statement is still useful as a presentation/intermediate wrapper because:

- it matches the existing arbitrary commit-arm theorem exactly;
- it avoids introducing measurability requirements;
- it is likely a direct one-theorem specialization;
- it gives later proof scripts both common RHS shapes;
- it finishes the local oracle probability wrapper saturation before moving to measurability or concrete argmax.

Exact Lean-facing statement

```lean
theorem ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hchoose_argmax :
      forall scores : Fin K -> Rat, forall a : Fin K,
        scores a <= scores (oracle.choose scores))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => if a = model.bestArm then 0 else tail a)
```

Local APIs/imports

Target file:

```lean
BanditRLProof.Algorithms.ETCMeasurability
```

Expected local dependencies:

```lean
ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail
ETC.CommitOracle
```

Optional route evidence:

```lean
ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail
ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
```

No new imports should be needed if the theorem is placed next to the existing oracle wrappers.

Intended proof route

Directly specialize the arbitrary commit-arm nonbest-tail theorem:

```lean
by
  exact
    ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail
      mu
      model
      (fun omega : Omega => oracle.choose (empMean omega))
      empMean
      tail
      (by
        intro omega a
        exact hchoose_argmax (empMean omega) a)
      hpair_tail
```

The proof should not use the filtered oracle theorem. It should consume the arbitrary if-zeroed theorem directly.

Regularity contracts

Require only:

```lean
[MeasurableSpace Omega]
mu : Measure Omega
model : FiniteBanditModel K
oracle : ETC.CommitOracle K
empMean : Omega -> Fin K -> Rat
tail : Fin K -> ENNReal
hchoose_argmax :
  forall scores : Fin K -> Rat, forall a : Fin K,
    scores a <= scores (oracle.choose scores)
hpair_tail :
  forall a : Fin K, (a = model.bestArm -> False) ->
    mu {omega : Omega |
      empMean omega a >= empMean omega model.bestArm} <= tail a
```

Do not require:

```lean
[MeasureTheory.IsProbabilityMeasure mu]
Measurable (fun omega => oracle.choose (empMean omega))
Measurable empMean
MeasurableSet {omega | oracle.choose (empMean omega) = model.bestArm -> False}
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
```

Retrieval evidence

Local declaration evidence:

```lean
ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail
```

This is the exact arbitrary commit-arm theorem being specialized.

```lean
ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail
ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
```

These show the oracle specialization pattern already works for nearby wrappers.

Mathlib evidence:

No new Mathlib search should be needed. The if-zeroed RHS is already supplied by the existing local arbitrary theorem. Therefore this leaf should not depend on fragile Mathlib lemmas such as `Finset.sum_filter`, `Finset.sum_ite`, or custom `by_cases` sum rewriting.

Use Mathlib only transitively for:

```lean
Finset.univ
Finset.sum
ite
ENNReal
Measure
```

Status

`project-local compiled leaf`

Not imported.
Not a port candidate.
Not a Mathlib candidate.
Not theorem-card-only.

Failure policy

If the direct specialization fails:

- Inspect the exact statement of:

  ```text
  python3 tools/bandit.py list-lean-decls ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail --statement
  ```

- If it expects an empirical-dominance premise, prove:

  ```lean
  intro omega
  exact hchoose_argmax (empMean omega) model.bestArm
  ```

- If it expects a subset premise, reuse:

  ```lean
  ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
  ```

- Do not prove a new finite-sum equivalence in this batch.
- Do not weaken or strengthen the regularity assumptions just to appease elaboration.

If the arbitrary theorem's RHS is not definitionally the same as the target RHS, stop and make a tiny separate normalization lemma only after confirming the exact mismatch. Do not mix that normalization proof into this leaf unless it is a one-line `simpa`.

Candidates not to attempt in the same batch

Do not attempt Candidate B in this batch.

```lean
ETC.measurableSet_commitOracle_ne_bestArm
```

It is useful, but it belongs to the measurability-contract branch. It should come after the probability wrapper family is saturated.

Do not attempt Candidate C in this batch.

`ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD`

Concrete finite argmax construction is a different layer. The current oracle/probability layer is not yet fully saturated until the if-zeroed oracle wrapper compiles.
