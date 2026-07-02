# Extended Pro Review Response: After Finite-Union Wrong-Mean Probability Wrapper

- Date: 2026-06-30
- Tool/model: ChatGPT Extended Pro via Chrome fallback after in-app browser interaction timeouts
- URL: https://chatgpt.com/c/6a42db09-187c-83ee-b2d4-23336db2e341
- Prompt file: `reports/extended_pro_after_finite_union_wrong_mean_prob_candidate_prompt_2026-06-30.md`
- Boundary:
  `ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM`
- Recorded from raw response:
  `reports/extended_pro_after_finite_union_wrong_mean_prob_raw_response_2026-06-30.txt`

## Reviewer Decision

- Chosen next leaf: `ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS`
- Classification: project-local elementary probability assembly missing-leaf
- Status: reviewer-approved
- Do not start in the same batch: empirical-mean construction/denominator positivity or pairwise tail wrapper.

## Exact Lean-Facing Statement

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega)) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        mu {omega : Omega | (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm})
```

## Imports And Local APIs

Add the theorem after the existing compiled leaves in
`BanditRLProof/Algorithms/ETCMeasurability.lean`.  No new import should be
needed.  Main local declarations:

```lean
ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset
ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum
```

The only general API needed is `le_trans`; the earlier finite-union wrapper
already absorbed `MeasureTheory.measure_biUnion_finset_le`.

## Intended Proof Route

Compose the two compiled inequalities:

1. wrong-commit event is bounded by the existential wrong-mean event;
2. existential wrong-mean event is bounded by the finite sum of guarded pairwise
   wrong-mean events.

Use `le_trans`; if Lean cannot infer the middle term, switch to an explicit
`calc` block.

## Regularity Contracts

Required:

```lean
[MeasurableSpace Omega]
(mu : Measure Omega)
(model : FiniteBanditModel K)
(commitArm : Omega -> Fin K)
(empMean : Omega -> Fin K -> Rat)
(hcommit_argmax :
  forall omega : Omega, forall a : Fin K,
    empMean omega a <= empMean omega (commitArm omega))
```

Not required: probability-measure instance, `Measurable commitArm`,
`hmeas_empMean`, `MeasurableSpace (Fin K)`, `MeasurableSingletonClass (Fin K)`,
concentration, filtration, empirical-mean construction, or final regret
assumptions.

## Retrieval Evidence

- Local compiled declaration:
  `ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset`.
- Local compiled declaration:
  `ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`.
- Mathlib/order evidence: `le_trans`.
- Mathlib finite-union evidence is already packaged by the previous wrapper via
  `MeasureTheory.measure_biUnion_finset_le`.

## Failure Policy

If positional arguments fail, first use the reviewer-provided `calc` proof to
pin the middle event.  If names fail, inspect exact local declarations via:

```powershell
python3 tools\bandit.py list-lean-decls prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset --statement
python3 tools\bandit.py list-lean-decls prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum --statement
```

Do not pivot to empirical-mean construction/denominator positivity or pairwise
tail wrapper until this assembly leaf compiles.

## Raw Extended Pro Response

See `reports/extended_pro_after_finite_union_wrong_mean_prob_raw_response_2026-06-30.txt`.
