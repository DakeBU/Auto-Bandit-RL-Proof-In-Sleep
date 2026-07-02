# Local Dual Review After Concrete Argmax

Date: 2026-06-30

Boundary before review:

- `ETC-COMMIT-ORACLE-CONCRETE-ARGMAX`

Review mode:

- Local two-agent review.
- No Extended Pro query.

Agent A recommendation:

- Selected leaf:
  `ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL`
- Reason:
  It is the narrowest compiled post-argmax bridge.  It specializes the already
  compiled abstract oracle filtered-sum pairwise-tail consumer to
  `ETC.argmaxCommitOracle` by supplying `ETC.argmaxCommitOracle_choose_spec`.
  It does not prove pairwise tails, introduce concentration, build filtration,
  or prove final ETC regret.

Agent B recommendation:

- Selected route-card:
  `ETC-PAIRWISE-TAIL-IMPORT-ROUTE-CARD`
- Reason:
  After concrete argmax, the real mathematical blocker is the source of the
  abstract `hpair_tail` hypothesis consumed by the probability wrappers.

Decision:

- Implement Agent A's compiled glue leaf first:
  `ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL`.
- Defer Agent B's `ETC-PAIRWISE-TAIL-IMPORT-ROUTE-CARD` to the next post-wrapper
  route decision.

Exact Lean-facing statement:

```lean
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose (empMean omega) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail
```

Local APIs/imports:

- `BanditRLProof.Algorithms.ETCArgmaxOracle`
- `ETC.argmaxCommitOracle`
- `ETC.argmaxCommitOracle_choose_spec`
- `ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`

Intended proof route:

1. Instantiate the abstract oracle filtered-sum pairwise-tail consumer with
   `oracle := ETC.argmaxCommitOracle hK`.
2. Discharge its argmax certificate using
   `ETC.argmaxCommitOracle_choose_spec hK`.
3. Pass through the existing abstract `hpair_tail` hypothesis unchanged.

Regularity contracts:

- `[MeasurableSpace Omega]`
- `hK : 0 < K`
- `mu : MeasureTheory.Measure Omega`
- `model : FiniteBanditModel K`
- `empMean : Omega -> Fin K -> Rat`
- `tail : Fin K -> ENNReal`
- Abstract non-best pairwise-tail assumptions only.

Retrieval evidence:

- `ETC.argmaxCommitOracle`
- `ETC.argmaxCommitOracle_choose_spec`
- `ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`

Status:

- `project-local`
- Compiled local Lean proof after implementation.

Failure policy:

- If the filtered RHS shape mismatches, stop and record a route mismatch.
- Do not pivot in the same batch to Hoeffding, sub-Gaussian tails, martingales,
  filtration/history, conditional expectation, or final ETC regret.
