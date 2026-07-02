# Extended Pro Review Response: After Abstract Commit-Oracle Argmax Consumer

- Prompt: `reports/extended_pro_after_commit_oracle_argmax_candidate_prompt_2026-06-30.md`
- URL: https://chatgpt.com/c/6a430d86-def8-83ee-ba00-fb92b2d119c4
- Boundary: `ETC-COMMIT-ORACLE-ARGMAX-CONSUMER`
- Chosen next leaf: Candidate A, `ETC-COMMIT-ORACLE-PROB-WRAPPER`

## Raw Extended Pro Response

## Review of completed leaf

The completed leaf is reasonable.

It is a clean **oracle-layer set-inclusion consumer**:

```lean
wrong oracle commit
→ oracle chose an arm different from bestArm
→ by abstract argmax certificate, chosen arm has empirical mean ≥ bestArm empirical mean
→ exists non-best arm with empirical mean ≥ bestArm empirical mean
```

This is the right granularity because it:

* does **not** construct a concrete argmax oracle;
* does **not** require oracle measurability;
* does **not** introduce probability, concentration, filtration, or expectation;
* reuses the already-local wrong-commit inclusion infrastructure;
* keeps the future concrete-argmax route separate from the probability assembly route.

## Selected next leaf: Candidate A

Choose:

```text
ETC-COMMIT-ORACLE-PROB-WRAPPER
```

This is the natural next bridge because the local oracle set-inclusion theorem is now ready to be consumed by the already-compiled arbitrary-measure probability wrapper.

Candidate B is useful but lower priority: event measurability is not needed for the existing arbitrary-measure union-bound-style probability assembly. Candidate C should wait until the abstract oracle probability path is saturated.

---

## Exact Lean-facing statement

Recommended declaration name:

```lean
theorem ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail
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
    (hpairwise_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
      oracle.choose (empMean omega) = model.bestArm -> False} <=
      (Finset.univ : Finset (Fin K)).sum tail
```

If the already-compiled theorem

```lean
ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail
```

uses slightly different notation for the final sum, mirror its conclusion exactly. Do not change the mathematical contract in this batch.

---

## Intended proof route

The proof should be a direct specialization of the existing arbitrary-commit-arm theorem with:

```lean
commitArm := fun omega : Omega => oracle.choose (empMean omega)
```

Skeleton:

```lean
theorem ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail
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
    (hpairwise_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
      oracle.choose (empMean omega) = model.bestArm -> False} <=
      (Finset.univ : Finset (Fin K)).sum tail := by
  refine ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail
    mu
    model
    (fun omega : Omega => oracle.choose (empMean omega))
    empMean
    tail
    ?hsubset
    hpairwise_tail
  exact
    ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
      model
      oracle
      empMean
      hchoose_argmax
```

If the argument order of `ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail` differs, keep the same proof structure and fill holes with `refine`.

---

## Local APIs/imports

No new Mathlib import should be needed if this is added to the same file:

```lean
BanditRLProof.Algorithms.ETCMeasurability
```

If placed in a new file, import the module containing both:

```lean
ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail
ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
```

Expected local dependencies:

```lean
ETC.CommitOracle
ETC.CommitOracle.choose
FiniteBanditModel
FiniteBanditModel.bestArm
ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail
ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
```

Expected Mathlib-level APIs already transitively available:

```lean
Measure
MeasurableSpace
ENNReal
Finset.univ
Finset.sum
Fin K
Set.Subset
```

---

## Regularity contracts

This leaf should require only:

```lean
[MeasurableSpace Omega]
(mu : Measure Omega)
```

It should **not** require:

```lean
[MeasureTheory.IsProbabilityMeasure mu]
Measurable empMean
Measurable fun omega => oracle.choose (empMean omega)
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
```

The only oracle regularity contract is the abstract argmax certificate:

```lean
hchoose_argmax :
  forall scores : Fin K -> Rat, forall a : Fin K,
    scores a <= scores (oracle.choose scores)
```

The only probability-side contract is the pairwise-tail assumption:

```lean
hpairwise_tail :
  forall a : Fin K, (a = model.bestArm -> False) ->
    mu {omega : Omega |
      empMean omega a >= empMean omega model.bestArm} <= tail a
```

---

## Retrieval evidence

| Source            | Evidence                                                            | Use                                                                                                     |
| ----------------- | ------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------- |
| Local declaration | `ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle` | Supplies the required wrong-commit subset for the oracle-specialized commit arm.                        |
| Local declaration | `ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail`                | Existing arbitrary-measure probability assembly; should be specialized, not reproved.                   |
| Local API         | `ETC.CommitOracle.choose`                                           | Defines the commit arm as `fun omega => oracle.choose (empMean omega)`.                                 |
| Local API         | `FiniteBanditModel.bestArm`                                         | Defines the wrong-commit event and non-best-arm guard.                                                  |
| Mathlib           | `Measure`, `ENNReal`, `Finset.univ.sum`                             | Existing measure and finite-sum infrastructure. No new theorem-level Mathlib search should be required. |

---

## Status

```text
project-local
```

This should be a compiled local theorem, not a theorem-card-only row, not a Mathlib candidate, and not a port candidate.

---

## Failure policy

1. First inspect the current statement:

```bash
python3 tools/bandit.py list-lean-decls ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail --statement
```

2. Match its exact tail-sum shape and argument order.

3. If the proof fails only because of definitional equality around the event, use:

```lean
  simpa using ...
```

around the application of the arbitrary commit-arm theorem.

4. If the existing probability wrapper has a different `hpairwise_tail` contract, do **not** reprove the finite union bound in this batch. Either:

   * mirror the existing contract exactly in the oracle wrapper, or
   * stop and record the mismatch as the next micro-leaf.

5. Do not introduce a concrete argmax oracle, measurability proof, concentration inequality, filtration, conditional expectation, or final ETC theorem as a fallback.

---

## Do not attempt in the same batch

Do **not** attempt Candidate B in this batch:

```text
ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY
```

It is useful later, but it belongs after the probability wrapper unless a later theorem explicitly requires measurable events.

Do **not** attempt Candidate C in this batch:

```text
ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD
```

The abstract oracle path is not saturated until the probability wrapper exists. Concrete finite argmax construction is a separate Mathlib/API-risk branch.

