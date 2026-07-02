# Extended Pro Review: After Filtered-Sum Pairwise-Tail Consumer

Date: 2026-06-30

Prompt: `reports/extended_pro_after_filtered_sum_pairwise_tail_candidate_prompt_2026-06-30.md`

Boundary: `ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL`

## Batch Verdict

Extended Pro judged the filtered-sum pairwise-tail consumer reasonable.  It
converted the if-zeroed RHS into the cleaner finite sum over non-best arms
while preserving the compiled probability proof.

## Selected Next Leaf

Extended Pro selected Candidate A:

`ETC-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS`

This is a deterministic Nat-level denominator positivity leaf for the ETC
exploration count.  It is not a full empirical-mean definition and not a
concentration theorem-card.

## Lean-Facing Statement

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos
    {K : Nat}
    (spec : ETC.Spec K)
    (commitArm : Fin K)
    (a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    0 < pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K)
```

## Proof Route

Use the compiled exact-count theorem
`ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq` to rewrite the
left-hand pull count to `spec.explorationPulls`, then close with
`hexplorationPulls_pos`.

## Contracts

The only new mathematical contract is
`hexplorationPulls_pos : 0 < spec.explorationPulls`.  Do not add measures,
measurability, probability assumptions, empirical means, casts, concentration,
filtration, or `0 < K`.

## Failure Policy

If the actionWithCommit equality theorem has a different argument order, use a
named `hcount` and rewrite explicitly.  If that equality is missing, fall back
to the narrower `ETC.pullCount_exploreArm_explorationPulls_mul_K_pos`.  Stop
after the positivity theorem compiles.
