## Review of completed leaf

The completed leaf is reasonable and well-scoped.

It is a pure measurability bridge:

```lean
coordinatewise empMean measurable
  -> empMean-vector measurable
  -> oracle.choose ∘ empMean measurable
```

It does **not** introduce probability, concentration, argmax correctness, oracle optimality, or regret. The assumptions are heavier than mathematically ideal, but they match the already-compiled local wrappers. In particular, `[MeasurableSingletonClass (Fin K -> Rat)] [Countable (Fin K -> Rat)]` are appropriate because the existing oracle-choice wrapper treats an arbitrary oracle choice function as measurable through a countable/discrete empirical-mean-vector domain. Mathlib’s measurable-space API supports this pattern: `MeasurableSingletonClass` gives measurable singletons, countable singleton-measurable spaces induce discreteness, and functions out of a discrete measurable domain are measurable. ([Lean Community][1])

## Selected next leaf

Choose **Candidate A**:

`ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES`

This is the correct next local bridge. It closes the direct route from coordinatewise empirical-mean measurability to wrong-commit event measurability, without attempting any new semantic/probabilistic content.

## Exact Lean-facing statement

The candidate statement is acceptable as written. I would use exactly:

```lean
theorem ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    [MeasurableSpace (Fin K)]
    [MeasurableSingletonClass (Fin K)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    MeasurableSet
      {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False}
```

No extra `[Countable (Fin K)]` should be needed. No explicit `[MeasurableSpace (Fin K -> Rat)]` should be added unless Lean unexpectedly fails to synthesize the Pi measurable-space instance from `[MeasurableSpace Rat]`.

## Intended proof route

Expected proof:

```lean
by
  have hchoose :
      Measurable (fun omega : Omega => oracle.choose (empMean omega)) :=
    ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
      (oracle := oracle)
      (empMean := empMean)
      hmeas_coord
  exact
    ETC.measurableSet_commitOracle_ne_bestArm
      (model := model)
      (oracle := oracle)
      (empMean := empMean)
      hchoose
```

This should be a two-local-wrapper composition.

If the existing wrong-event wrapper uses `≠` instead of the implication-to-`False` spelling, use:

```lean
  simpa [Ne] using
    ETC.measurableSet_commitOracle_ne_bestArm
      (model := model)
      (oracle := oracle)
      (empMean := empMean)
      hchoose
```

## Local APIs / imports

Implement in the same module:

```lean
BanditRLProof.Algorithms.ETCMeasurability
```

Expected local dependencies:

```lean
ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
ETC.measurableSet_commitOracle_ne_bestArm
```

Transitive local dependencies already established:

```lean
ETC.measurable_empMeanVector_of_forall_measurable
ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
```

Mathlib-level support is only through standard measurable-space infrastructure: `Measurable` is defined by measurable preimages, and `Measurable.comp'` supports composition of measurable maps. ([Lean Community][1]) The singleton/equality-event side is supported by `MeasurableSingletonClass`, `MeasurableSet.singleton`, and `measurableSet_eq`. ([Lean Community][1])

## Regularity contracts

This leaf should require only:

```lean
[MeasurableSpace Omega]
[MeasurableSpace Rat]
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
[MeasurableSingletonClass (Fin K -> Rat)]
[Countable (Fin K -> Rat)]
```

plus the coordinatewise empirical-mean measurability hypothesis:

```lean
hmeas_coord :
  forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)
```

It should **not** require:

```lean
Measure Omega
MeasureTheory.IsProbabilityMeasure
independence
filtration
adaptedness
integrability
oracle correctness
argmax correctness
tie-breaking correctness
concentration assumptions
```

The oracle remains abstract. This leaf proves only that the wrong-commit event is measurable.

## Retrieval evidence

Local evidence from the current boundary:

```lean
ETC.measurable_empMeanVector_of_forall_measurable
ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
ETC.measurableSet_commitOracle_ne_bestArm
```

The newly completed coordinatewise oracle-choice bridge supplies exactly the measurable choice map needed by the existing wrong-event wrapper.

Mathlib evidence:

* `Measurable` is a preimage-based predicate, so event measurability from a measurable map into `Fin K` is the expected route. ([Lean Community][1])
* `MeasurableSingletonClass` supplies measurable singleton/equality events; this is why `[MeasurableSingletonClass (Fin K)]` belongs in Candidate A even though it was not needed by the oracle-choice measurability wrapper. ([Lean Community][1])
* Countable measurable-singleton spaces are promoted to discrete measurable spaces, which explains the assumptions used by the arbitrary-oracle-choice wrapper. ([Lean Community][1])

## Status

**Project-local.**

This is not a Mathlib candidate and not an imported theorem. It is a repository-specific composition lemma over `FiniteBanditModel`, `ETC.CommitOracle`, and the project’s empirical-mean abstraction.

## Failure policy

If the exact proof fails:

1. Run:

   ```lean
   #check ETC.measurableSet_commitOracle_ne_bestArm
   #check ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
   ```

2. Match the exact target spelling of `ETC.measurableSet_commitOracle_ne_bestArm`.

3. If the existing wrapper targets `≠`, keep the theorem statement above and close with:

   ```lean
   simpa [Ne] using ...
   ```

4. If typeclass synthesis fails for `(Fin K -> Rat)`, add an explicit local assumption only if the checked local wrapper already requires it:

   ```lean
   [MeasurableSpace (Fin K -> Rat)]
   ```

   Otherwise do not strengthen the theorem.

5. Do not replace this with a direct proof unless the local wrong-event wrapper is unusable. The point of the leaf is to compose the already-compiled bridge layer.

## Do not attempt in the same batch

Do **not** attempt Candidate B in this batch. A concrete finite argmax-backed `ETC.CommitOracle K` introduces tie-breaking, finite search, and argmax correctness obligations. That is a different route-card layer.

Do **not** attempt Candidate C in this batch. Pairwise empirical-mean tails require concentration-side contracts: measurability, independence, filtration/adaptedness, boundedness or integrability, and probability assumptions. That belongs after the current abstract measurability/oracle layer is saturated.

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html "Mathlib.MeasureTheory.MeasurableSpace.Defs"
