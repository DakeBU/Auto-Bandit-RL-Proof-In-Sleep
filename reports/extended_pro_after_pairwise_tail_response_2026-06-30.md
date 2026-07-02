# Extended Pro Review: After Abstract Pairwise-Tail Consumer

Date: 2026-06-30

Prompt: `reports/extended_pro_after_pairwise_tail_candidate_prompt_2026-06-30.md`

Boundary: `ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL`

## Batch Verdict

Extended Pro judged the completed `ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail`
batch reasonable.  The proof added an abstract pairwise-tail consumer without
starting Hoeffding, sub-Gaussian, filtration, or empirical-mean construction.

The recorded build, test, declaration lookup, reference-index, review-status,
global check, and unfinished-ledger steps were sufficient.

## Selected Next Leaf

Extended Pro selected Candidate A, but recommended the lower-risk `if`-zeroed
`Finset.univ.sum` shape before a true `Finset.filter` theorem:

`ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL`

## Lean-Facing Statement

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail
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
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => if a = model.bestArm then 0 else tail a)
```

## Proof Route

Use `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events` directly, then
prove a pointwise summand bound with `Finset.sum_le_sum`.  The best-arm branch
is empty and closes against the zero branch.  The non-best branch erases the
guard by measure monotonicity and applies `hpair_tail`.

## Contracts

This remains project-local and arbitrary-measure.  It should not require a
probability measure, measurable `commitArm`, measurable `empMean`, event
measurability, empirical-mean construction, actual concentration, filtration,
conditional expectation, or final ETC regret.

## Failure Policy

If the best-arm branch does not simplify, prove the guarded event is empty by
`ext omega`. If measure monotonicity does not resolve, use `mu.mono`. If the
summand functions cause elaboration trouble, introduce a local `Guard`
abbreviation.

Do not implement the filtered `Finset.filter` theorem, empirical-mean
construction, or concentration route discovery in the same batch.
