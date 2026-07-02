# Extended Pro Review Response: After Oracle If-Zeroed Nonbest Probability Wrapper

- Date: 2026-06-30
- Tool/model: ChatGPT Extended Pro
- URL: https://chatgpt.com/c/6a431c50-6298-83e8-a2b8-6c6f16091455
- Prompt file: `reports/extended_pro_after_commit_oracle_nonbest_candidate_prompt_2026-06-30.md`
- Local gate before review: `python3 tools\bandit.py check`
- Boundary:
  `ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL`
- Recorded from raw response:
  `reports/extended_pro_after_commit_oracle_nonbest_raw_2026-06-30.md`

## Reviewer Decision

- Chosen next leaf: ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY
- Classification: project-local
- Status: reviewer-approved

## Exact Lean-Facing Statement

```lean
theorem ETC.measurableSet_commitOracle_ne_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_choose :
      Measurable (fun omega : Omega => oracle.choose (empMean omega))) :
    MeasurableSet
      {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False}
```

## Imports And Local APIs

- `BanditRLProof.Algorithms.ETCMeasurability`
- `ETC.measurableSet_commitArm_ne_bestArm`
- `ETC.CommitOracle`

## Intended Proof Route

1. Specialize `ETC.measurableSet_commitArm_ne_bestArm` with
   `commitArm := fun omega => oracle.choose (empMean omega)`.
2. Pass `hmeas_choose` directly as the composed-choice measurability
   assumption.

## Regularity Contracts

- `[MeasurableSpace Omega]`
- `[MeasurableSpace (Fin K)]`
- `[MeasurableSingletonClass (Fin K)]`
- Direct assumption:
  `Measurable (fun omega => oracle.choose (empMean omega))`
- No measure, probability instance, concrete oracle construction,
  empirical-mean measurability proof, concentration, filtration, or final ETC
  theorem.

## Retrieval Evidence

- Existing compiled `ETC.measurableSet_commitArm_ne_bestArm`.
- Existing oracle probability wrappers already use the same event shape
  `{omega | oracle.choose (empMean omega) = model.bestArm -> False}`.

## Failure Policy

- Keep this as a direct composed-choice measurability wrapper.
- Do not attempt concrete argmax construction, pairwise-tail import work,
  concentration, filtration, or final ETC theorem in the same batch.

## Raw Extended Pro Response

## Review of the completed leaf

`ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail` is a reasonable completed leaf.

It is correctly scoped because it only specializes the already-compiled arbitrary commit-arm probability consumer to

```lean
commitArm omega := oracle.choose (empMean omega)
```

and keeps all hard future obligations abstract:

* no concrete argmax construction;
* no measurability of `oracle.choose` as a function on score vectors;
* no empirical-mean concentration;
* no filtration or independence;
* no final ETC regret theorem.

The if-zeroed nonbest sum is also the right final-facing shape:

```lean
(Finset.univ : Finset (Fin K)).sum
  (fun a => if a = model.bestArm then 0 else tail a)
```

because it avoids carrying a filtered `Finset` while still exposing that the best arm contributes zero.

## Selected next leaf: Candidate A

Choose:

```text
ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY
```

This is the only candidate that should be attempted now. It is a small compiled project-local leaf and closes the natural measurability counterpart of the oracle wrong-commit event. Mathlib’s measurable-function contract is exactly about measurable preimages, and `MeasurableSingletonClass` supplies measurable singletons / equality events, so this leaf is aligned with the existing measure-theoretic API rather than adding new theory. ([Lean Community][1])

## Exact Lean-facing statement

```lean
theorem ETC.measurableSet_commitOracle_ne_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_choose :
      Measurable (fun omega : Omega => oracle.choose (empMean omega))) :
    MeasurableSet
      {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False}
```

## Local APIs/imports

Add this in the same file:

```lean
BanditRLProof.Algorithms.ETCMeasurability
```

No new import should be necessary if the existing theorem is already in scope:

```lean
ETC.measurableSet_commitArm_ne_bestArm
```

Expected local dependency:

```lean
theorem ETC.measurableSet_commitArm_ne_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (hmeas_commit : Measurable commitArm) :
    MeasurableSet
      {omega : Omega | commitArm omega = model.bestArm -> False}
```

Mathlib-side regularity support:

* `Measurable f` means preimages of measurable sets are measurable. ([Lean Community][1])
* `MeasurableSingletonClass` gives measurable singletons, and Mathlib exposes `MeasurableSet.singleton` / `measurableSet_eq`. ([Lean Community][1])

## Intended proof route

Use the already-compiled arbitrary commit-arm event measurability lemma by specialization.

```lean
theorem ETC.measurableSet_commitOracle_ne_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_choose :
      Measurable (fun omega : Omega => oracle.choose (empMean omega))) :
    MeasurableSet
      {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False} := by
  simpa using
    (ETC.measurableSet_commitArm_ne_bestArm
      (model := model)
      (commitArm := fun omega : Omega => oracle.choose (empMean omega))
      (hmeas_commit := hmeas_choose))
```

This should be a one-proof-line wrapper after the theorem header.

## Regularity contracts

Required:

```lean
[MeasurableSpace Omega]
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
hmeas_choose :
  Measurable (fun omega : Omega => oracle.choose (empMean omega))
```

Not required:

```lean
Measure Omega
MeasureTheory.IsProbabilityMeasure mu
Measurable empMean
Measurable oracle.choose
concrete argmax oracle
independence
filtration
integrability
concentration
```

The direct composed measurability assumption is intentional. It prevents this leaf from becoming an oracle-construction or empirical-mean-measurability theorem.

## Retrieval evidence

Local:

* Existing compiled `ETC.measurableSet_commitArm_ne_bestArm`.
* Existing oracle probability wrappers already use the same event:

  ```lean
  {omega | oracle.choose (empMean omega) = model.bestArm -> False}
  ```

Mathlib:

* `Measurable` is defined through measurable preimages. ([Lean Community][1])
* `MeasurableSingletonClass` and `MeasurableSet.singleton` support equality-event measurability over `Fin K`. ([Lean Community][1])

## Status

```text
project-local compiled leaf
```

Not theorem-card-only. This should be implemented and checked locally.

Recommended verification:

```bash
lake build BanditRLProof.Algorithms.ETCMeasurability
lake build Tests
python3 tools/bandit.py list-lean-decls ETC.measurableSet_commitOracle_ne_bestArm --statement
python3 tools/bandit.py unfinished
python3 tools/bandit.py check
```

## Failure policy

If the specialization proof fails:

1. First check theorem order: the new theorem must appear after `ETC.measurableSet_commitArm_ne_bestArm`.

2. If elaboration fails, bind the composed commit arm explicitly:

   ```lean
   let commitArm : Omega -> Fin K :=
     fun omega => oracle.choose (empMean omega)
   ```

3. If `simpa` fails, prove through an intermediate `have`:

   ```lean
   have h :
       MeasurableSet
         {omega : Omega |
           (fun omega : Omega => oracle.choose (empMean omega)) omega =
             model.bestArm -> False} :=
     ETC.measurableSet_commitArm_ne_bestArm
       (model := model)
       (commitArm := fun omega : Omega => oracle.choose (empMean omega))
       (hmeas_commit := hmeas_choose)
   simpa using h
   ```

4. Do **not** respond by adding oracle measurability, empirical-mean measurability, argmax construction, concentration assumptions, or probability-measure assumptions.

## Candidates not to attempt in this batch

Do **not** attempt Candidate B in the same batch. A finite argmax route is useful later, but it touches construction choices: `Finset` max/image APIs, project-local recursion, or wrapper design. Mathlib has finite maximum APIs such as `Finset.max'`, but choosing a stable argmax route is a separate theorem-card task, not needed for the current local event layer. ([Lean Community][2])

Do **not** attempt Candidate C in the same batch. Mathlib now has sub-Gaussian/Hoeffding-style declarations, including `measure_sum_ge_le_of_iIndepFun`, Hoeffding’s lemma, and Azuma-Hoeffding statements, but connecting them to the current pairwise empirical-mean tail assumption requires measurability, independence, reward sampling, coercions from `Rat`/real-valued empirical means, and filtration/integrability contracts. ([Lean Community][3])

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html "Mathlib.MeasureTheory.MeasurableSpace.Defs"
[2]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Max.html "Mathlib.Data.Finset.Max"
[3]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/SubGaussian.html "Mathlib.Probability.Moments.SubGaussian"
