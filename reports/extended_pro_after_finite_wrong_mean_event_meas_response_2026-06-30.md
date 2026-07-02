# Extended Pro Review Response: After Finite Wrong-Mean Event Measurability

- Date: 2026-06-30
- Tool/model: ChatGPT Extended Pro
- URL: https://chatgpt.com/c/6a42db09-187c-83ee-b2d4-23336db2e341
- Prompt file: `reports/extended_pro_after_finite_wrong_mean_event_meas_candidate_prompt_2026-06-30.md`
- Local gate before review: `python3 tools\bandit.py check`
- Boundary:
  `ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM`
- Recorded from raw response:
  `reports/extended_pro_after_finite_wrong_mean_event_meas_raw_response_2026-06-30.txt`

## Reviewer Decision

- Chosen next leaf: ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM
- Classification: project-local finite-union probability-wrapper missing-leaf
- Status: reviewer-approved

## Exact Lean-Facing Statement

```lean
ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum: measure of finite existential wrong-mean event is bounded by the finite sum of guarded pairwise wrong-mean event measures
```

## Imports And Local APIs

Mathlib.MeasureTheory.OuterMeasure.Basic if needed; current ETCMeasurability imports may already expose measure_biUnion_finset_le

## Intended Proof Route

rewrite existential wrong-mean event as a bounded union over Finset.univ; apply measure_biUnion_finset_le; no measurability or probability instance required

## Regularity Contracts

[MeasurableSpace Omega], mu : Measure Omega, model : FiniteBanditModel K, empMean : Omega -> Fin K -> Rat; no hmeas_empMean, probability instance, commitArm, argmax, concentration, filtration, empirical-mean construction, or final theorem

## Retrieval Evidence

Mathlib measure_biUnion_finset_le in OuterMeasure.Basic; local finite wrong-mean event measurability compiled; Finset.univ finite-arm style used locally

## Failure Policy

only repair measure_biUnion_finset_le import/signature or bounded-union set equality; do not move to empirical-mean construction or pairwise tails until this wrapper compiles

## Raw Extended Pro Response

Pick: Candidate A

Choose the finite-union probability upper bound. This is the next clean wrapper after event measurability: it closes the elementary union-bound layer before any empirical-mean construction or concentration work.

1. Exact Lean-facing statement
lean
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

Do not add hmeas_empMean here. The finite union bound is an outer-measure/subadditivity fact and should remain independent of event measurability.

2. Local APIs/imports

Current imports are likely sufficient if measure_biUnion_finset_le is already visible through the current import closure:

lean
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import BanditRLProof.Core

If Lean cannot resolve the union-bound theorem, add the direct import:

lean
import Mathlib.MeasureTheory.OuterMeasure.Basic

Main APIs:

lean
Finset.univ : Finset (Fin K)

measure_biUnion_finset_le

Finset.sum

The previously compiled event-measurability theorem is not needed for the proof, but it is useful downstream when combining this wrapper with measurable probability statements.

3. Intended proof route

Define the guarded pairwise event:

lean
let E : Fin K -> Set Omega := fun a =>
  {omega : Omega | (a = model.bestArm -> False) /\
    empMean omega a >= empMean omega model.bestArm}

Then prove:

lean
{omega : Omega |
  exists a : Fin K, (a = model.bestArm -> False) /\
    empMean omega a >= empMean omega model.bestArm}
=
⋃ a in (Finset.univ : Finset (Fin K)), E a

by extensionality and simp.

Then apply measure_biUnion_finset_le.

Robust proof skeleton:

lean
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
          empMean omega a >= empMean omega model.bestArm}) := by
  classical
  let E : Fin K -> Set Omega := fun a =>
    {omega : Omega | (a = model.bestArm -> False) /\
      empMean omega a >= empMean omega model.bestArm}
  have hset :
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}
      =
      (⋃ a in (Finset.univ : Finset (Fin K)), E a) := by
    ext omega
    simp [E]
  rw [hset]
  simpa [E] using
    (measure_biUnion_finset_le
      (μ := mu)
      (s := (Finset.univ : Finset (Fin K)))
      (t := E))

The final line may need minor argument-order adjustment depending on the exact local signature of measure_biUnion_finset_le.

4. Regularity contracts

Required:

lean
[MeasurableSpace Omega]
(mu : Measure Omega)
(model : FiniteBanditModel K)
(empMean : Omega -> Fin K -> Rat)

Not required:

lean
[MeasureTheory.IsProbabilityMeasure mu]
hmeas_empMean
Measurable commitArm
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]

No stochastic assumptions are introduced.

5. Retrieval evidence

Use the locally found Mathlib theorem:

lean
measure_biUnion_finset_le

from:

lean
Mathlib.MeasureTheory.OuterMeasure.Basic

The finite event measurability leaf already confirms that the existential wrong-mean event is naturally represented as a finite Finset.univ union:

lean
ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm

The existing local style already uses:

lean
Finset.univ : Finset (Fin K)

for finite arm enumeration.

6. Status classification

Project-local.

The underlying measure inequality is imported from Mathlib, but this wrapper is project-specific because it mentions:

lean
FiniteBanditModel K
model.bestArm
empMean : Omega -> Fin K -> Rat

It is not theorem-card-only; it should be a small local Lean proof.

7. Failure policy

If the named-argument version of measure_biUnion_finset_le fails, inspect its exact signature and try one of these shapes:

lean
  simpa [E] using
    (measure_biUnion_finset_le mu
      (Finset.univ : Finset (Fin K)) E)

or:

lean
  exact measure_biUnion_finset_le
    (μ := mu)
    (s := (Finset.univ : Finset (Fin K)))
    (t := E)

If simp [E] does not prove hset, expand the membership proof manually:

lean
  have hset :
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}
      =
      (⋃ a in (Finset.univ : Finset (Fin K)), E a) := by
    ext omega
    constructor
    · intro h
      rcases h with ⟨a, ha_ne, ha_ge⟩
      refine Set.mem_iUnion.mpr ?_
      refine ⟨a, ?_⟩
      refine Set.mem_iUnion.mpr ?_
      exact ⟨Finset.mem_univ a, ha_ne, ha_ge⟩
    · intro h
      simp [E] at h
      exact h

Do not move to empirical-mean construction or pairwise tails until this wrapper compiles. This is the last obvious elementary probability wrapper before the proof DAG starts depending on how empMean is actually constructed or how concentration assumptions are encoded.
