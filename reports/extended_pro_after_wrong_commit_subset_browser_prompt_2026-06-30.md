# ABRL Extended Pro Review: After Wrong-Commit Set Inclusion

Current Lean 4 status:

- Deterministic fixed-commit ETC layer compiles through best-arm commit/suffix regret facts.
- Wrong-commit theorem-card target remains the probability bridge:
  `mu {omega | commitArm omega != bestArm} <= mu {omega | exists non-best a, empMean omega a >= empMean omega bestArm}`.
- Two local subleaves now compile in `BanditRLProof.Algorithms.ETCMeasurability`:

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

`python3 tools/bandit.py check` passed after this.

Pick exactly one next leaf. Do not start Hoeffding, sub-Gaussian, martingale,
filtration, conditional expectation, UCB, TS, EXP3, Tsallis-INF, OFUL, RL, or
final theorem work.

Candidate A: measure wrapper using `Measure.mono`.

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

Candidate B: pairwise empirical-mean comparison measurability.

```lean
theorem ETC.measurableSet_empMean_ge_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean : forall a : Fin K, Measurable (fun omega => empMean omega a))
    (a b : Fin K) :
    MeasurableSet {omega : Omega | empMean omega a >= empMean omega b}
```

Candidate C: finite existential wrong-mean event measurability.

```lean
theorem ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean : forall a : Fin K, Measurable (fun omega => empMean omega a)) :
    MeasurableSet {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm}
```

Candidate D: stop/import-route first.

Required answer:
1. Pick A/B/C/D.
2. Give exact Lean statement.
3. Imports/local APIs.
4. Proof route.
5. Regularity contracts and assumptions to avoid.
6. Retrieval evidence.
7. Classification.
8. Failure policy.
