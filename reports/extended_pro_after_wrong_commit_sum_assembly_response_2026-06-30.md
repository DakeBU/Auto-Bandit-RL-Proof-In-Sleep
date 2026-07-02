# Extended Pro Review: After Wrong-Commit Sum Assembly

Date: 2026-06-30

Prompt: `reports/extended_pro_after_wrong_commit_sum_assembly_candidate_prompt_2026-06-30.md`

Thread: <https://chatgpt.com/c/6a42db09-187c-83ee-b2d4-23336db2e341>

Boundary: `ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS`

## Selected Leaf

Extended Pro selected Candidate A:

`ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL`

This should be implemented as a project-local wrapper in
`BanditRLProof/Algorithms/ETCMeasurability.lean`.

## Lean-Facing Statement

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum tail
```

## Rationale

This is the right next leaf because it consumes the already compiled
wrong-commit finite-sum assembly and exposes the interface that later
concentration leaves must prove. It does not mix in empirical-mean construction,
denominator positivity, filtration, independence, or Hoeffding.

Candidate B should wait for a separate empirical-mean construction design.
Candidate C can be added later as a filtered-tail sharpening.

## Proof Route

1. Use `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`.
2. Apply `Finset.sum_le_sum`.
3. In the best-arm branch, prove the guarded event is empty.
4. In each non-best branch, use `mu.mono` to drop the guard and apply
   `hpair_tail`.

## Contracts

The theorem remains arbitrary-measure and project-local. It requires only:

- `hcommit_argmax`, the empirical argmax contract for `commitArm`;
- `hpair_tail`, an abstract non-best pairwise tail bound.

It must not require:

- a probability-measure instance;
- measurability of `commitArm` or `empMean`;
- event measurability;
- filtration or conditional expectation;
- independence;
- sub-Gaussian or Hoeffding hypotheses.

## Failure Policy

If `simp [h]` does not close the best-arm branch, prove the event is `empty`
explicitly with `ext omega`. If the non-best subset is not inferred, introduce
an explicit `hsubset` and use `mu.mono hsubset`.

Do not begin the empirical-mean construction leaf or the filtered-tail
sharpening leaf in the same implementation batch.
