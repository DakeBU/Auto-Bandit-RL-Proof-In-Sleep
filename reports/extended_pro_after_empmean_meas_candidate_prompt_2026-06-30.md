# Prompt For Extended Pro: Next Leaf After ETC Empirical-Mean Measurability

We are working in the Lean project `Auto-Bandit-RL-Proof-In-Sleep`.

Current compiled boundary:

- `ETC.empMeanAtExploration` and
  `ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls` compile.
- `ETC.measurable_sumRewards_actionWithCommit_exploration` compiles as the
  numerator-measurability bridge.
- `ETC.measurable_empMeanAtExploration_of_measurable_div_const` compiles as
  the full empirical-mean measurability theorem under an explicit
  `hdiv_const`.
- `measurable_rat_div_const` compiles under
  `[MeasurableSpace Rat] [MeasurableSingletonClass Rat]`.
- `ETC.measurable_empMeanAtExploration` now compiles with no explicit
  `hdiv_const`:

```lean
theorem ETC.measurable_empMeanAtExploration
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      ETC.empMeanAtExploration spec commitArm (reward omega) a)
```

The wrong-commit probability consumer layer is already compiled and consumes:

```lean
hcommit_argmax :
  forall omega : Omega, forall a : Fin K,
    empMean omega a <= empMean omega (commitArm omega)
```

and abstract pairwise tails of the form:

```lean
hpair_tail :
  forall a : Fin K, (a = model.bestArm -> False) ->
    mu {omega : Omega |
      empMean omega a >= empMean omega model.bestArm} <= tail a
```

Please choose exactly one next leaf. Do not choose a broad theorem such as full
ETC regret, UCB regret, Thompson sampling, EXP3, Tsallis-INF, OFUL, or RL/MDP.

Candidate A: commit argmax wiring.

Use the existing local surface:

```lean
structure ETC.CommitOracle (K : Nat) where
  choose : (Fin K -> Rat) -> Fin K
```

Design exactly one deterministic wrapper that turns an explicit oracle argmax
contract into the `hcommit_argmax` shape consumed by the probability wrappers.
Do not prove oracle optimality, commit-arm measurability, concentration, or
final ETC theorem in the same batch.

Candidate B: empirical-mean coordinate bundle/wrapper.

Design exactly one wrapper that packages the compiled
`ETC.measurable_empMeanAtExploration` as coordinate measurability for

```lean
fun omega : Omega =>
  fun a : Fin K =>
    ETC.empMeanAtExploration spec commitArm (reward omega) a
```

if this is the better bridge before argmax wiring. Do not introduce an argmax
oracle or concentration in the same batch.

Candidate C: pairwise concentration route card.

Create only the theorem-card/import-route decision for the exact pairwise tail
assumption needed after plugging in the compiled
`ETC.empMeanAtExploration` API. Do not prove Hoeffding/sub-Gaussian yet.

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
