# Prompt For Extended Pro: Next Leaf After ETC Empirical Mean Definition

We are working in the Lean project `Auto-Bandit-RL-Proof-In-Sleep`.

Current boundary:

- `ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION` is now compiled locally.
- Implemented declarations:

```lean
def ETC.empMeanAtExploration
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) : Rat :=
  sumRewards (ETC.actionWithCommit spec commitArm) reward a
      (spec.explorationPulls * K) /
    (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat)

theorem ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) :
    ETC.empMeanAtExploration spec commitArm reward a =
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
          (spec.explorationPulls * K) /
        ((spec.explorationPulls : Nat) : Rat)
```

This is deterministic only.  No probability, stochastic reward law, argmax,
filtration, or concentration theorem was introduced.

Relevant compiled local APIs:

```lean
ETC.actionWithCommit
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero
measurable_sumRewards
ETC.measurableSet_empMean_ge_empMean
ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm
ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail
```

Current `unfinished` boundary:

> Ask reviewer/Extended Pro again before choosing argmax/measurability wiring
> for the new empirical-mean API or the actual pairwise concentration route.

Important local observation:

- The numerator measurability route appears straightforward by applying
  `measurable_sumRewards` to the constant action trace
  `fun _ : Omega => ETC.actionWithCommit spec commitArm` and a stochastic
  reward trace `reward : Omega -> RewardTrace Rat`.
- The full empirical-mean measurability theorem may need an explicit
  division-measurability import or wrapper, because `Measurable.div_const`
  consumes `MeasurableDiv Rat` / `MeasurableDiv.measurable_div_const`.
- We should not guess a broad Rat/Real probability route without a precise leaf.

Please choose exactly one next leaf.  Do not choose a broad theorem such as
ETC regret, Hoeffding, sub-Gaussian concentration, filtration, conditional
expectation, UCB, Thompson sampling, EXP3, Tsallis-INF, OFUL, or RL/MDP.

Candidate A: numerator measurability only.

```lean
theorem ETC.measurable_sumRewards_actionWithCommit_exploration
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K))
```

Candidate B: empirical-mean measurability with an explicit division-by-constant
contract, avoiding a premature import decision.

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

Candidate C: Mathlib/Rat division-measurability import or wrapper leaf.

Find the exact import/API for making `x / c : Rat` measurable as a function
of `x`, or add a project-local wrapper if Mathlib has the theorem but not an
instance under our imports.  This should not mention ETC except as motivation.

Candidate D: deterministic commit-arm/argmax wiring only.

Define a deterministic commit helper from a supplied `choose : (Fin K -> Rat) -> Fin K`
and `ETC.empMeanAtExploration`, then prove only an abstract argmax consumer
under an explicit `hchoose_argmax` contract.  No stochastic measurability or
probability.

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
