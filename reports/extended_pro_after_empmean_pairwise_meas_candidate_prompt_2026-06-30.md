# Extended Pro Candidate Prompt: After Pairwise Empirical-Mean Event Measurability

We are working in the ABRL Lean 4 project:

`D:\code\Auto-Bandit-RL-Proof-In-Sleep-main\Auto-Bandit-RL-Proof-In-Sleep-main`

Current local gate:

```bash
python3 tools\bandit.py check
```

passes.

## Current Compiled Boundary

The current Lean file is:

```lean
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import BanditRLProof.Core

namespace BanditRLProof
namespace ETC
```

The following wrong-commit/probability-facing leaves now compile locally:

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

## Local Retrieval Evidence

Local Mathlib search found:

- `Finset.measurableSet_biUnion` in
  `Mathlib.MeasureTheory.MeasurableSpace.Defs`
- `MeasurableSet.iUnion` in
  `Mathlib.MeasureTheory.MeasurableSpace.Defs`
- the existing compiled local pairwise event wrapper above
- `Finset.univ : Finset (Fin K)` is already used broadly in this project

The current unfinished/backlog boundary says:

```text
BRL-OP-ETC-SUBGAUSS-001 next leaf:
ETC-MEAS-EMPMEAN-GE-EMPMEAN compiled; next choose finite existential/union event measurability
```

## Candidate A: finite existential wrong-mean event measurability

Attempt this as the next local Lean theorem:

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

Likely route:

```lean
classical
change MeasurableSet
  (⋃ a in (Finset.univ : Finset (Fin K)),
    {omega : Omega | (a = model.bestArm -> False) /\
      empMean omega a >= empMean omega model.bestArm})
exact Finset.measurableSet_biUnion _ (fun a ha => ...)
```

Inside each arm event, use a constant propositional condition intersected with
the compiled pairwise event:

```lean
ETC.measurableSet_empMean_ge_empMean empMean hmeas_empMean a model.bestArm
```

The proof may need `by_cases h : a = model.bestArm`, then simplify:

- if `h`, event is empty;
- otherwise event is the pairwise comparison event.

## Candidate B: finite union over all arms without non-best predicate

Attempt a weaker but simpler event:

```lean
theorem ETC.measurableSet_exists_empMean_ge_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    MeasurableSet {omega : Omega |
      exists a : Fin K, empMean omega a >= empMean omega model.bestArm}
```

This may be easier but is less aligned with the existing wrong-commit event.

## Candidate C: stop and do not implement yet

Choose this only if the exact finite existential event statement should be
reshaped before any Lean proof attempt.

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

Do not select Hoeffding, sub-Gaussian, martingale, filtration, conditional
expectation, UCB/TS/EXP3/Tsallis/OFUL/RL, or final theorem work.
