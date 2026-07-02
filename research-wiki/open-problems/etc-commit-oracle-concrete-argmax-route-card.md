# ETC Commit Oracle Concrete Argmax Route Card

Status: compiled-local.

Decision source:

- Local dual-agent review:
  `reports/local_dual_review_after_oracle_wrong_event_coord_meas_decision_2026-06-30.md`
- Boundary before route choice:
  `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES`

## Leaf

`ETC-COMMIT-ORACLE-CONCRETE-ARGMAX`

## Exact Lean-Facing Statement Shape

The route card has been promoted into local Lean declarations in
`BanditRLProof.Algorithms.ETCArgmaxOracle`:

```lean
noncomputable def ETC.argmaxCommitOracle
    {K : Nat} (hK : 0 < K) : ETC.CommitOracle K

theorem ETC.argmaxCommitOracle_choose_spec
    {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Rat) (a : Fin K) :
    scores a <= scores ((ETC.argmaxCommitOracle hK).choose scores)
```

The compiled wrapper documents how the concrete theorem feeds the abstract
consumer:

```lean
theorem ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_argmaxOracle
    {Omega : Type u} {K : Nat}
    (hK : 0 < K)
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat) :
    {omega : Omega |
      (ETC.argmaxCommitOracle hK).choose (empMean omega) =
        model.bestArm -> False} <=
    {omega : Omega |
      exists a : Fin K,
        (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}
```

This wrapper is a direct consumer of the compiled abstract lemma
`ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle` and
`ETC.argmaxCommitOracle_choose_spec`.

## Local APIs And Imports

Implemented imports:

```lean
import BanditRLProof.Algorithms.ETCMeasurability
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Basic
```

Local APIs already available:

- `ETC.CommitOracle K`
- `ETC.argmaxCommitOracle`
- `ETC.argmaxCommitOracle_choose_spec`
- `ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_argmaxOracle`
- `ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle`
- `ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail`
- `ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`
- `ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail`
- `ETC.measurable_commitOracle_choose_of_forall_measurable_empMean`
- `ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean`

## Intended Proof Route

1. Establish a finite nonempty domain from `hK : 0 < K`, giving an inhabitant
   of `Fin K`.
2. Choose a score-maximizing arm by scanning `List.finRange K`.
3. Use deterministic foldl tie-breaking that keeps the previous arm on ties.
4. Prove the maximality certificate by reusing the same foldl-select invariant
   pattern as `FiniteBanditModel.mean_le_bestArm_mean`:
   `forall scores a, scores a <= scores ((ETC.argmaxCommitOracle hK).choose scores)`.
5. Feed that certificate into the already compiled abstract oracle consumers.
6. Reuse existing countable-score-vector and coordinatewise empirical-mean
   measurability wrappers for stochastic statements; do not reprove
   measurability inside the argmax construction unless Mathlib gives it for
   free.

## Regularity Contracts

- Require `hK : 0 < K`; do not rely on an implicit impossible inhabitant for
  `Fin 0`.
- Scores remain `Fin K -> Rat`.
- Use the existing linear order on `Rat`.
- The route card does not require a probability measure, empirical-mean
  construction, sub-Gaussian assumption, filtration, conditional expectation,
  or final ETC regret theorem.
- If the tie-breaking proof is more expensive than the maximality proof, split
  it into a later helper leaf.

## Retrieval Evidence

Local declaration lookup shows the abstract surface is already present:

```text
BanditRLProof.ETC.CommitOracle
BanditRLProof.ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
BanditRLProof.ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail
BanditRLProof.ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
BanditRLProof.ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail
BanditRLProof.ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
BanditRLProof.ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean
```

This means the concrete finite argmax-backed `ETC.CommitOracle K` and its
maximality certificate are now local compiled declarations.  The remaining
missing work is still the actual pairwise concentration/tail route, filtration,
and final ETC theorem, not this deterministic argmax surface.

## Status

`compiled-local`.

Compiled through:

```bash
python3 tools/bandit.py check
```

## Failure Policy

The implementation used the project-local `List.finRange` fold route instead
of a Mathlib `Finset.max'` route.  Do not pivot in the same batch to pairwise
concentration, filtration/history, conditional expectation, or the final ETC
theorem.
