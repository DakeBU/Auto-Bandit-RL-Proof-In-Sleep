# Extended Pro Review Prompt: After Wrong-Commit Sum Assembly

- Date: 2026-06-30
- Current boundary:
  `ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS`
- Local gate before this prompt: `python3 tools\bandit.py check` passed after
  compiling the boundary leaf.

## Current Lean-Compiled ETC Probability Layer

In `BanditRLProof/Algorithms/ETCMeasurability.lean`, the following ETC
probability/event leaves compile:

```lean
ETC.measurableSet_commitArm_ne_bestArm
ETC.measurableSet_empMean_ge_empMean
ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm
ETC.wrong_commit_subset_exists_empMean_ge_bestArm
ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset
ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum
ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events
```

The newest compiled theorem is:

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

It composes the wrong-commit-to-existential-event measure wrapper with the
finite-union wrong-mean probability wrapper.  It does not introduce a
probability-measure instance, event measurability, empirical-mean construction,
filtration, pairwise tail theorem, concentration theorem, or final ETC theorem.

## Current Ledger Status

`python3 tools\bandit.py unfinished` now records:

```text
BRL-OP-ETC-SUBGAUSS-001 next leaf:
`ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS` compiled;
next ask reviewer to choose empirical-mean construction/denominator positivity,
abstract pairwise tail wrapper, or next ETC probability assembly
```

The theorem card still says ETC is missing empirical-mean construction, pairwise
concentration/tails, filtration, and final ETC theorem.

## Decision Needed

Please choose exactly one next leaf row. Do not choose a broad theorem such as
"prove Hoeffding", "formalize sub-Gaussian", "build a filtration", "prove ETC
regret", or "finish UCB/TS/EXP3/Tsallis/OFUL/RL". We need one Lean-facing leaf
that is small enough to compile before the next reviewer checkpoint.

Candidate A: abstract unguarded pairwise-tail wrapper

This would consume a per-non-best-arm abstract tail assumption for the unguarded
pairwise empirical-mean comparison event and combine it with the compiled
wrong-commit sum assembly.

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

Possible proof route:

1. use `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`;
2. apply `Finset.sum_le_sum`;
3. for `a = model.bestArm`, the guarded event is empty;
4. for `a != model.bestArm`, use measure monotonicity from the guarded event to
   the unguarded pairwise event and then `hpair_tail`.

This does not prove the tail bound; it only packages how a future tail theorem
will be consumed.

Candidate B: empirical-mean construction / denominator positivity design leaf

Choose a precise deterministic or measurability-only local statement connecting
the project ETC exploration trace, `sumRewards`, and `pullCount` to a
well-defined empirical mean.  Keep it small.  For example, it may expose a
denominator positivity or nonzero-denominator theorem for the exploration
horizon before defining any probabilistic tail theorem.

Please give the exact Lean statement if this is chosen.

Candidate C: sharper filtered non-best tail wrapper

Instead of Candidate A's loose `(Finset.univ).sum tail`, prove a wrapper whose
right-hand side sums only over non-best arms, for example with a filtered
`Finset.univ` or an `if a = model.bestArm then 0 else tail a` expression.

Please choose this only if the filtered Finset proof is still a small wrapper
and better than first compiling Candidate A.

## Required Output Format

For the chosen leaf, write:

- exact Lean-facing statement;
- local APIs/imports;
- intended proof route;
- regularity contracts;
- retrieval evidence from Mathlib/LML/local declarations;
- status: imported, port candidate, Mathlib candidate, project-local, or theorem-card-only;
- failure policy.

Also explicitly say which candidates should not be started in the same batch.
