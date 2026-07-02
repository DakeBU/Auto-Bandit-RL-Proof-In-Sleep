# Prompt For Extended Pro: Next Leaf After Full ETC Empirical-Mean Measurability

We are working in the Lean project `Auto-Bandit-RL-Proof-In-Sleep`.

Current compiled boundary:

- `ETC.empMeanAtExploration` and
  `ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls` compile.
- `ETC.measurable_sumRewards_actionWithCommit_exploration` compiles as the
  numerator-measurability bridge for fixed-commit ETC empirical means under
  stochastic reward traces.
- `ETC.measurable_empMeanAtExploration_of_measurable_div_const` now compiles:

```lean
theorem ETC.measurable_empMeanAtExploration_of_measurable_div_const
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (hdiv_const : forall c : Rat, Measurable (fun x : Rat => x / c)) :
    Measurable (fun omega : Omega =>
      ETC.empMeanAtExploration spec commitArm (reward omega) a)
```

This leaf deliberately kept `hdiv_const` explicit.  It did not add a
Mathlib/Rat division-measurability import, commit argmax wiring, actual
concentration/tail theorem, filtration, conditional expectation, or final ETC
theorem.

The already compiled wrong-commit probability consumer expects an explicit
argmax contract:

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

Please choose exactly one next leaf.  Do not choose a broad theorem such as
full ETC regret, Hoeffding, UCB, Thompson sampling, EXP3, Tsallis-INF, OFUL, or
RL/MDP.

Candidate A: Mathlib/Rat division measurability import or wrapper.

Decide whether the next leaf should discharge the explicit contract

```lean
forall c : Rat, Measurable (fun x : Rat => x / c)
```

from a narrow Mathlib import / existing instance / local wrapper.  If yes,
give the exact import and Lean-facing statement.  If the statement is not
available under the current arbitrary `[MeasurableSpace Rat]` assumptions,
say so and propose the smallest correct replacement contract.

Candidate B: commit argmax wiring.

Use the existing local structure:

```lean
structure ETC.CommitOracle (K : Nat) where
  choose : (Fin K -> Rat) -> Fin K
```

Design exactly one deterministic wrapper that converts an explicit oracle
argmax contract into the `hcommit_argmax` shape consumed by the probability
wrappers.  Do not prove oracle optimality, measurability of the chosen arm, or
concentration in the same batch.

Candidate C: pairwise concentration route card.

Create only the theorem-card/import-route decision for the exact pairwise tail
assumption needed after plugging in the compiled
`ETC.empMeanAtExploration` API.  Do not prove Hoeffding/sub-Gaussian yet.

For the selected leaf, please write:

- exact Lean-facing statement;
- local APIs/imports;
- intended proof route;
- regularity contracts;
- retrieval evidence from Mathlib/LML/local declarations;
- status: imported, port candidate, Mathlib candidate, project-local, or
  theorem-card-only;
- failure policy.

Failure-policy constraint for this batch:

- Implement exactly the selected leaf.
- Do not start actual concentration, filtration, conditional expectation,
  final ETC theorem, UCB, TS, EXP3, Tsallis-INF, OFUL, or RL/MDP work.
