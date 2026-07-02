# Extended Pro Review Response: After Oracle Pairwise-Tail Probability Wrapper

- Prompt: `reports/extended_pro_after_commit_oracle_prob_candidate_prompt_2026-06-30.md`
- URL: `https://chatgpt.com/c/6a4310c7-cbe8-83ee-abad-602277de56cc`
- Boundary: `ETC-COMMIT-ORACLE-PROB-WRAPPER`
- Chosen next leaf: `ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL`
- Extraction note: the page-level `复制回复` action copied the user prompt in this run, so the raw assistant response below was extracted from the ChatGPT message DOM.

## Raw Extended Pro Response

Review of completed leaf

The completed leaf is reasonable and correctly scoped.

It is a good project-local wrapper because it does exactly one useful thing:

```lean
commitArm omega := oracle.choose (empMean omega)
```

and then reuses the already-compiled arbitrary commit-arm probability consumer. It also keeps the abstraction boundary intact:

no concrete argmax implementation;

no measurability of oracle.choose;

no probability-space assumption;

no concentration inequality;

no filtration;

no final ETC regret theorem.

The hypothesis

```lean
hchoose_argmax :
  forall scores : Fin K -> Rat, forall a : Fin K,
    scores a <= scores (oracle.choose scores)
```

is the correct abstract contract for the oracle layer. It is stronger than needed for some later variants, but it is clean and matches the deterministic wrong-commit inclusion already compiled.

The current layer is not yet saturated, because the oracle specialization still exists only for the coarser unfiltered `Finset.univ.sum tail` bound. The next natural step is to expose the sharper filtered non-best-arm form.

Selected next leaf: Candidate B

Leaf

`ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL`

This should be attempted next.

Candidate B is preferable to Candidate A because the filtered sum is the canonical statement:

```lean
sum over a in {a | a != bestArm}, tail a
```

whereas Candidate A's if-zeroed `Finset.univ.sum` shape is mostly a normalization/convenience wrapper. Candidate B is also more directly aligned with the pairwise wrong-mean event decomposition: only non-best arms generate wrong-commit events.

Candidate C is useful later, but it is orthogonal to the measure upper-bound chain. Since the current probability wrappers deliberately avoid measurability requirements, the event-measurability wrapper should not interrupt the probability-layer saturation sequence.

Exact Lean-facing statement

Use the same style as the latest completed theorem.

```lean
theorem ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
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
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail
```

If the existing local filtered theorem uses `a != model.bestArm` instead of the implication-to-false spelling, then use the project's established spelling. Given the existing theorem statements shown in the prompt, I would keep:

```lean
a = model.bestArm -> False
```

for maximum consistency.

Local APIs / imports

The declaration should live in:

```lean
BanditRLProof.Algorithms.ETCMeasurability
```

Expected imports should already be available from that file. No new heavy imports should be needed.

Relevant local declarations:

```lean
ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail
ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail
```

The new theorem should not depend on the previous oracle wrapper. It should specialize the arbitrary filtered consumer directly.

Expected Mathlib/local ingredients:

```lean
Finset.univ
Finset.filter
Finset.sum
Measure
MeasurableSpace
ENNReal
```

The proof should only need `classical` for decidability of the filtered predicate.

Intended proof route

The proof should be a direct specialization of the already compiled arbitrary commit-arm filtered consumer.

Skeleton:

```lean
theorem ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
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
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail := by
  classical
  exact
    ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail
      (mu := mu)
      (model := model)
      (commitArm := fun omega : Omega => oracle.choose (empMean omega))
      (empMean := empMean)
      (tail := tail)
      ?hwrong_subset
      hpair_tail
```

The missing argument should be discharged by the oracle wrong-commit inclusion:

```lean
  exact
    ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
      (model := model)
      (oracle := oracle)
      (empMean := empMean)
      hchoose_argmax
```

So the expected full proof shape is:

```lean
by
  classical
  exact
    ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail
      (mu := mu)
      (model := model)
      (commitArm := fun omega : Omega => oracle.choose (empMean omega))
      (empMean := empMean)
      (tail := tail)
      (ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
        (model := model)
        (oracle := oracle)
        (empMean := empMean)
        hchoose_argmax)
      hpair_tail
```

If the arbitrary filtered theorem has a named hypothesis order different from the above, use named arguments for every non-obvious argument and fill the subset proof explicitly.

Regularity contracts

The theorem should require only:

```lean
[MeasurableSpace Omega]
```

and should not require:

```lean
[MeasureTheory.IsProbabilityMeasure mu]
Measurable empMean
Measurable fun omega => oracle.choose (empMean omega)
MeasurableSet {omega | oracle.choose (empMean omega) = model.bestArm -> False}
```

It should also not require:

```lean
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
```

unless the already compiled arbitrary filtered theorem requires them. Given the latest completed probability wrapper did not require them, this one should not either.

The oracle contract remains purely order-theoretic:

```lean
hchoose_argmax :
  forall scores : Fin K -> Rat, forall a : Fin K,
    scores a <= scores (oracle.choose scores)
```

The tail contract remains pairwise and non-best-arm restricted:

```lean
hpair_tail :
  forall a : Fin K, (a = model.bestArm -> False) ->
    mu {omega : Omega |
      empMean omega a >= empMean omega model.bestArm} <= tail a
```

Retrieval evidence

Local declarations:

```lean
ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail
ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail
```

Mathlib / LML evidence:

The new theorem should not need new Mathlib facts beyond what the arbitrary filtered theorem already used internally. The wrapper itself should require only:

```lean
Finset.filter
Finset.sum
Finset.univ
```

plus ordinary theorem application.

No new LML retrieval should be necessary unless elaboration fails due to theorem argument order or implicit arguments.

Status

`project-local`

This is not a Mathlib candidate. It is specific to the project's ETC oracle/probability abstraction and naming scheme.

It is also not theorem-card-only. It should be a short compiled Lean wrapper.

Failure policy

If the direct proof fails, do not broaden the task.

Acceptable fixes:

Inspect the exact statement of:

```lean
ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail
```

using:

```text
python3 tools/bandit.py list-lean-decls ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail --statement
```

Adjust only:

- argument order;
- named arguments;
- the exact filtered predicate spelling;
- whether the subset lemma must be passed as a named hypothesis.

If the filtered theorem uses `a != model.bestArm`, bridge locally by rewriting the predicate, but avoid proving a general Finset filter equivalence unless absolutely necessary.

If the conclusion's filtered sum is syntactically different from the existing arbitrary theorem's conclusion, match the existing theorem exactly rather than adding a normalization lemma in this batch.

Do not introduce:

```lean
Measurable fun omega => oracle.choose (empMean omega)
```

Do not construct a concrete argmax oracle.

Do not add concentration, finite exploration empirical means, filtration, or regret decomposition.

Candidates not to attempt in the same batch

Do not attempt Candidate A in this batch.

Reason: the if-zeroed nonbest sum is weaker or at least less canonical than the filtered non-best-arm sum. It can be added later as a presentation wrapper if needed.

Do not attempt Candidate C in this batch.

Reason: event measurability is a separate regularity branch. The current probability wrappers intentionally avoid needing it. Adding it now would mix the probability-tail saturation path with a measurability path and risks expanding the batch unnecessarily.

The next exact leaf should therefore be:

`ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL`
