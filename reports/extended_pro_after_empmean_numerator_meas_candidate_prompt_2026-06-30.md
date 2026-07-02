# Prompt For Extended Pro: Next Leaf After ETC Numerator Measurability

We are working in the Lean project `Auto-Bandit-RL-Proof-In-Sleep`.

Current compiled boundary:

- `ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION` is compiled locally:

```lean
def ETC.empMeanAtExploration
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) : Rat

theorem ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) :
    ETC.empMeanAtExploration spec commitArm reward a =
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
          (spec.explorationPulls * K) /
        ((spec.explorationPulls : Nat) : Rat)
```

- `ETC-MEASURABLE-SUMREWARDS-ACTION-WITH-COMMIT-EXPLORATION` is compiled locally:

```lean
theorem ETC.measurable_sumRewards_actionWithCommit_exploration
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K))
```

The last `unfinished` boundary says:

> Ask reviewer/Extended Pro again before choosing division/full empirical-mean
> measurability, argmax wiring, or the actual pairwise concentration route.

Relevant local APIs:

```lean
ETC.empMeanAtExploration
ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls
ETC.measurable_sumRewards_actionWithCommit_exploration
ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero
ETC.measurableSet_empMean_ge_empMean
ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail
```

Local smoke-test evidence:

The following theorem shape compiles in a scratch Lean file when `hdiv_const`
is explicit:

```lean
example {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (hdiv_const : forall c : Rat, Measurable (fun x : Rat => x / c)) :
    Measurable (fun omega : Omega =>
      ETC.empMeanAtExploration spec commitArm (reward omega) a) := by
  have hnum : Measurable (fun omega : Omega =>
      sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K)) :=
    ETC.measurable_sumRewards_actionWithCommit_exploration
      spec commitArm a reward hreward
  have hdiv : Measurable (fun omega : Omega =>
      sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K) /
        (pullCount (ETC.actionWithCommit spec commitArm) a
          (spec.explorationPulls * K) : Rat)) := by
    exact (hdiv_const _).comp hnum
  simpa [ETC.empMeanAtExploration] using hdiv
```

Please choose exactly one next leaf.  Do not choose a broad theorem such as
ETC regret, Hoeffding, sub-Gaussian concentration, filtration, conditional
expectation, UCB, Thompson sampling, EXP3, Tsallis-INF, OFUL, or RL/MDP.

Candidate A: full empirical-mean measurability under explicit division-by-constant contract.

Leaf id:

```text
ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION-OF-DIV-CONST
```

Statement shape:

```lean
theorem ETC.measurable_empMeanAtExploration_of_measurable_div_const
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (hdiv_const : forall c : Rat, Measurable (fun x : Rat => x / c)) :
    Measurable (fun omega : Omega =>
      ETC.empMeanAtExploration spec commitArm (reward omega) a)
```

Candidate B: Mathlib/Rat division-measurability import or wrapper.

Find the exact import/API or local wrapper that turns `x / c : Rat` into a
measurable function of `x`.  This should be a small import-route wrapper and
should not mention ETC except in comments.

Candidate C: deterministic argmax/commit wiring.

Define a deterministic helper using `ETC.CommitOracle.choose` and
`ETC.empMeanAtExploration`, plus only an explicit argmax-consumer theorem.
No stochastic measurability, measure, probability, or concentration.

Candidate D: pairwise concentration route card.

Create only a theorem-card/import-route decision for the exact pairwise tail
assumption needed by the already compiled probability consumer.  Do not prove
Hoeffding/sub-Gaussian yet.

For the selected leaf, please write:

- exact Lean-facing statement;
- local APIs/imports;
- intended proof route;
- regularity contracts;
- retrieval evidence from Mathlib/LML/local declarations;
- status: imported, port candidate, Mathlib candidate, project-local, or theorem-card-only;
- failure policy.

Failure-policy constraint for this batch:

- Implement exactly the selected leaf.
- Do not start actual concentration, filtration, conditional expectation,
  final ETC theorem, UCB, TS, EXP3, Tsallis-INF, OFUL, or RL/MDP work.
