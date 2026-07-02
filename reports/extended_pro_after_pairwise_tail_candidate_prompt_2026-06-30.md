# Extended Pro Review Prompt: After Abstract Pairwise-Tail Consumer

You are reviewing a Lean 4 / Mathlib project:

Repository: Auto-Bandit-RL-Proof-In-Sleep

Current boundary:

`ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL`

The project is building a verified bandit/RL proof library.  We are moving
one small Lean-facing leaf at a time and must not jump directly to broad
theorems such as "prove UCB regret", "formalize Hoeffding", or
"formalize Tsallis-INF".

## Completed In This Batch

Extended Pro previously selected Candidate A, the abstract unguarded
pairwise-tail consumer wrapper.  It has now been implemented and checked.

Lean declaration:

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

Implementation file:

`BanditRLProof/Algorithms/ETCMeasurability.lean`

Test canary:

`Tests/Basic.lean`

Checks run successfully:

```text
lake build BanditRLProof.Algorithms.ETCMeasurability
lake build Tests
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-lean-decls ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail --statement
python3 tools/bandit.py review-status --prompt reports/extended_pro_after_wrong_commit_sum_assembly_candidate_prompt_2026-06-30.md --response-stem extended_pro_after_wrong_commit_sum_assembly --boundary ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS --json
python3 tools/bandit.py check
python3 tools/bandit.py unfinished
```

Docs updated:

- `research-wiki/theory-tree/mathlib-foundation-leaf-map.md`
- `research-wiki/open-problems/bandit-proof-backlog.md`
- `research-wiki/open-problems/etc-wrong-commit-probability-design.md`
- `docs/collaborator_unfinished_work_guide.md`
- `docs/completion_gap_audit.md`
- `docs/project_overview_next_plan.md`
- `proof-obligations/BRL-ETC-PORT-001.md`
- `tools/bandit.py`

The project now has four compiled local ETC probability wrappers:

1. `ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset`
2. `ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`
3. `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`
4. `ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail`

## Current Open Boundary

Do not start Hoeffding, sub-Gaussian, martingale, filtration, conditional
expectation, or final ETC/UCB theorem work unless you choose an exact small leaf.

Please evaluate whether this batch was reasonable and choose exactly one next
leaf.  I see three plausible directions:

## Candidate A: Filtered Nonbest Pairwise-Tail Wrapper

Sharpen the just-compiled wrapper so the RHS sums only over non-best arms.

Possible statement shape:

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
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => decide (a = model.bestArm -> False))).sum tail
```

Concern: this may require slightly more Finset/filter algebra than the current
probability layer wants.

## Candidate B: Empirical-Mean Construction / Denominator Positivity

Start the construction that will eventually justify `empMean` from
`sumRewards` and `pullCount`.

This likely needs a very small denominator-positivity or nonzero exploration
count leaf rather than a full empirical-mean definition.

Concern: statement design may depend on whether the project wants `Rat`,
`Real`, or `ENNReal.ofReal` empirical means first.

## Candidate C: Actual Pairwise Concentration Route Discovery

Do not prove concentration yet.  Instead, create a narrow import-route or
theorem-card leaf for the exact Mathlib/LML theorem shape needed to prove:

```lean
mu {omega : Omega |
  empMean omega a >= empMean omega model.bestArm} <= tail a
```

Concern: this may still be too broad unless it is limited to retrieval
evidence and an exact theorem-card contract.

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

Also state whether the completed pairwise-tail consumer batch was a reasonable
step and whether any documentation/check step is missing.
