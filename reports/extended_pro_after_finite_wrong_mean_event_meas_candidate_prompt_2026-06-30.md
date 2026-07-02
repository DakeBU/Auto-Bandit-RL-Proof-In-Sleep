# Extended Pro Candidate Prompt: After Finite Wrong-Mean Event Measurability

We are working in the ABRL Lean 4 project:

`D:\code\Auto-Bandit-RL-Proof-In-Sleep-main\Auto-Bandit-RL-Proof-In-Sleep-main`

Current local gate before this prompt:

```bash
lake build BanditRLProof.Algorithms.ETCMeasurability
lake build Tests
python3 tools\bandit.py list-lean-decls ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm --statement
```

all pass/find the declaration.

## Current Compiled Boundary

The following probability-facing ETC wrong-commit leaves now compile locally:

```lean
theorem ETC.measurableSet_commitArm_ne_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (hmeas_commit : Measurable commitArm) :
    MeasurableSet {omega : Omega | commitArm omega = model.bestArm -> False}
```

```lean
theorem ETC.measurableSet_empMean_ge_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a))
    (a b : Fin K) :
    MeasurableSet {omega : Omega | empMean omega a >= empMean omega b}
```

```lean
theorem ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    MeasurableSet {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm}
```

```lean
theorem ETC.wrong_commit_subset_exists_empMean_ge_bestArm
    {Omega : Type u} {K : Nat}
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega)) :
    Set.Subset
      {omega : Omega | commitArm omega = model.bestArm -> False}
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}
```

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset
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
    mu {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm}
```

## Local Retrieval Evidence

Mathlib/local search found:

- `measure_biUnion_finset_le` in
  `Mathlib.MeasureTheory.OuterMeasure.Basic`
- `measure_iUnion_le` and `measure_union_le` in the measure API
- `Finset.measurableSet_biUnion` already used by the compiled finite event
  measurability leaf
- local declaration:
  `ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm`

The backlog now says:

```text
BRL-OP-ETC-SUBGAUSS-001 next leaf:
ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM compiled;
next ask reviewer to choose finite-union probability bound,
empirical-mean construction, or pairwise tail wrapper.
```

## Candidate A: finite-union probability upper bound

Attempt a project-local measure wrapper such as:

```lean
theorem ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat) :
    mu {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        mu {omega : Omega | (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm})
```

Possible proof route:

1. rewrite the existential event as the bounded union over `Finset.univ`;
2. apply `measure_biUnion_finset_le`.

This should not require event measurability, probability measure, concentration,
filtration, or empirical-mean construction.

## Candidate B: empirical-mean construction regularity

Start defining/proving measurability and denominator positivity for the actual
ETC empirical mean constructed from reward traces and exploration samples.

This is important but likely wider because it touches reward sums, division,
nonzero denominators, and possibly reward trace assumptions.

## Candidate C: pairwise tail/concentration wrapper

Start the concentration route for

```text
Pr[empMean a >= empMean bestArm]
```

under sub-Gaussian or bounded rewards.

This is likely much wider because sub-Gaussian/Hoeffding imports and
regularity contracts are not yet settled locally.

## Candidate D: stop

Choose this only if the current exact event/probability route should be
redesigned before another Lean attempt.

## Request

Pick exactly one next leaf.  Please return:

1. exact Lean-facing statement;
2. local APIs/imports;
3. intended proof route;
4. regularity contracts;
5. retrieval evidence from Mathlib/local declarations;
6. status classification: imported, port candidate, Mathlib candidate,
   project-local, or theorem-card-only;
7. failure policy.

Do not select broad Hoeffding, sub-Gaussian, martingale, filtration,
conditional expectation, UCB/TS/EXP3/Tsallis/OFUL/RL, or final theorem work
unless you explicitly argue that all smaller probability-wrapper leaves are
now exhausted.
