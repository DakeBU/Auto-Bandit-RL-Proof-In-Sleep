# Extended Pro Review Prompt: After If-Zeroed Nonbest Pairwise-Tail Consumer

You are reviewing a Lean 4 / Mathlib project:

Repository: Auto-Bandit-RL-Proof-In-Sleep

Current boundary:

`ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL`

The project is building a verified bandit/RL proof library.  We are moving
one small Lean-facing leaf at a time.  Do not jump directly to broad theorems
such as "prove Hoeffding", "prove UCB regret", "formalize conditional
expectation", or "formalize Tsallis-INF".

## Completed In The Previous Batch

You previously recommended the lower-risk if-zeroed `Finset.univ.sum` wrapper
instead of the true `Finset.filter` theorem.  It has now been implemented and
checked.

Lean declaration:

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

Implementation file:

`BanditRLProof/Algorithms/ETCMeasurability.lean`

Test canary:

`Tests/Basic.lean`

Checks run successfully:

```text
lake build BanditRLProof.Algorithms.ETCMeasurability
lake build Tests
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-lean-decls ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail --statement
python3 tools/bandit.py review-status --prompt reports/extended_pro_after_pairwise_tail_candidate_prompt_2026-06-30.md --response-stem extended_pro_after_pairwise_tail --boundary ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL --json
python3 tools/bandit.py check
python3 tools/bandit.py unfinished
```

Current local ETC wrong-commit probability wrappers now compiled:

1. `ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset`
2. `ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`
3. `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`
4. `ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail`
5. `ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail`

The `unfinished` gate now says the next choice should be one of:

- true filtered-sum normalization;
- empirical-mean construction / denominator positivity;
- actual pairwise concentration route.

## Candidate A: True Filtered-Sum Normalization

Convert the if-zeroed RHS into a true filtered finite sum over non-best arms.

Possible theorem shape:

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

Concern: Lean may need careful handling of decidability and `Finset.sum_filter`
or `Finset.sum_congr`.

## Candidate B: Empirical-Mean Construction / Denominator Positivity

Start the construction that will eventually justify `empMean` from
`sumRewards` and `pullCount`.

Likely first leaf could be a very small count/positivity statement for the ETC
exploration horizon, not a full empirical-mean definition.

Concern: statement design may depend on whether the project should expose
`Rat`, `Real`, or `ENNReal.ofReal` empirical means first.

## Candidate C: Actual Pairwise Concentration Route Discovery

Do not prove concentration yet.  Create a narrow theorem-card or import-route
leaf for the exact Mathlib/LML theorem shape needed to prove each non-best
pairwise tail assumption:

```lean
mu {omega : Omega |
  empMean omega a >= empMean omega model.bestArm} <= tail a
```

Concern: this can still become too broad unless it is limited to retrieval
evidence, exact theorem-card contracts, and a failure policy.

## Requested Review Output

Pick exactly one next leaf and provide:

1. exact Lean-facing statement;
2. local APIs/imports;
3. intended proof route;
4. regularity contracts;
5. retrieval evidence from Mathlib/LML/local declarations;
6. status: imported, port candidate, Mathlib candidate, project-local, or
   theorem-card-only;
7. failure policy.

Also state whether the completed if-zeroed nonbest pairwise-tail consumer was
a reasonable step and whether any documentation/check step is missing.
