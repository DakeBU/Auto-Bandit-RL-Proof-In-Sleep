# Extended Pro Review: After If-Zeroed Nonbest Pairwise-Tail Consumer

Date: 2026-06-30

Prompt: `reports/extended_pro_after_nonbest_pairwise_tail_candidate_prompt_2026-06-30.md`

Boundary: `ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL`

## Batch Verdict

Extended Pro judged the if-zeroed nonbest pairwise-tail consumer reasonable.
It closed the probability consumer shape without entering empirical-mean
construction, concentration, or filtration.

## Selected Next Leaf

Extended Pro selected Candidate A:

`ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL`

This is a project-local finite-sum presentation normalization from the
if-zeroed RHS to a true `Finset.filter` RHS.

## Lean-Facing Statement

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail
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
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail
```

## Proof Route

Use `ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail` to get the
if-zeroed bound.  Prove the RHS equality with `Finset.sum_filter`,
`Finset.sum_congr`, and `by_cases h : a = model.bestArm`; then rewrite the
bound.

## Contracts

The theorem remains arbitrary-measure and project-local.  Do not add
measurability of `commitArm` or `empMean`, probability-measure assumptions,
empirical-mean definitions, denominator positivity, concentration,
filtration, or final ETC theorem work.

## Failure Policy

Repair only finite-sum normalization.  If `Finset.sum_filter` is not available,
add `Mathlib.Algebra.BigOperators.Group.Finset`.  Stop after this theorem
compiles.
