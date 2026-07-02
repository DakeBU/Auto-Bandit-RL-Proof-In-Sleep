# Extended Pro Review Response: After ETC CommitArm Wrong-Event Measurability

- Date: 2026-06-30
- Tool/model: ChatGPT Extended Pro
- URL: https://chatgpt.com/c/6a42ccc5-fb50-83ee-92e6-c1087132ae45
- Prompt file: `reports/extended_pro_after_commitarm_ne_bestarm_meas_candidate_prompt_2026-06-30.md`
- Local gate before review: `python3 tools\bandit.py check`
- Boundary:
  `ETC-MEAS-COMMITARM-NE-BESTARM`
- Recorded from raw response:
  `reports/extended_pro_after_commitarm_ne_bestarm_meas_raw_response_2026-06-30.txt`

## Reviewer Decision

- Chosen next leaf: ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT
- Classification: project-local missing-leaf
- Status: reviewer-approved

## Exact Lean-Facing Statement

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

## Imports And Local APIs

- No new probability or ordered-measurability imports.
- Local: `FiniteBanditModel`, `model.bestArm`, `Set.Subset`, `Rat` order already available through existing local imports.
- Suggested location: `BanditRLProof.Algorithms.ETCMeasurability` or a nearby event-reduction file.

## Intended Proof Route

1. Introduce arbitrary `omega` in the wrong-commit event.
2. Use witness `a := commitArm omega`.
3. Reuse the wrongness proof as the non-best witness proof.
4. Use `hcommit_argmax omega model.bestArm` to close the empirical comparison, with `change` if needed for `>=`.

## Regularity Contracts

- No `[MeasurableSpace Omega]`, no `[MeasurableSpace (Fin K)]`, no `Measure`, no probability instance.
- No measurable `commitArm` or `empMean` assumptions.
- No `spec`, `reward`, `hbest_gap_pos`, filtration, concentration, or final theorem facts.
- Valid for arbitrary `K : Nat`; the existence of `model.bestArm : Fin K` is part of `FiniteBanditModel K`.

## Retrieval Evidence

- Local: compiled `ETC.measurableSet_commitArm_ne_bestArm` confirms the wrong-commit event shape is accepted.
- Local: `FiniteBanditModel.bestArm` supplies the selected best arm.
- Mathlib: `Set.Subset`; later probability inequality can use measure monotonicity after this set inclusion.

## Failure Policy

- If the final inequality does not close directly, use `change empMean omega model.bestArm <= empMean omega (commitArm omega)`.
- If namespace elaboration fails, put the declaration inside `namespace ETC` and remove the prefix.
- Do not pivot to empirical-mean measurability, finite union, concentration, or final probability theorem in the same batch if this leaf fails.

## Raw Extended Pro Response

I will keep this at the theorem-card boundary and avoid concentration/probability expansion. The key decision is whether the next leaf should reduce proof risk or import risk.

---

1. Pick

Pick Candidate C: Pure Wrong-Commit Set Inclusion.

This is the next load-bearing leaf. It proves the actual event reduction used by the probability theorem, without adding ordered-measurability import risk. Mathlib’s Measure is defined as extending an outer measure, and μ s can be applied to arbitrary sets; monotonicity is available as Measure.mono, so the final measure inequality will only need this subset lemma, not measurability of the RHS event. 
Lean Community

2. Exact Lean-facing statement
lean
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

Suggested proof:

lean
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
          empMean omega a >= empMean omega model.bestArm} := by
  intro omega hwrong
  refine ⟨commitArm omega, hwrong, ?_⟩
  exact hcommit_argmax omega model.bestArm

More robust last line if >= does not close by definitional reduction:

lean
  change empMean omega model.bestArm <= empMean omega (commitArm omega)
  exact hcommit_argmax omega model.bestArm
3. Local APIs/imports

No new Mathlib import should be needed.

Required local/API ingredients:

lean
FiniteBanditModel K
model.bestArm : Fin K
commitArm : Omega -> Fin K
empMean : Omega -> Fin K -> Rat
Set.Subset

The theorem should live naturally in:

lean
BanditRLProof.Algorithms.ETCMeasurability

or a nearby event-reduction file if you split one later. Do not add Candidate A’s ordered-measurability imports in this batch.

4. Proof route

For arbitrary omega in the wrong-commit set:

Choose witness:

lean
a := commitArm omega

The wrongness proof is already:

lean
hwrong : commitArm omega = model.bestArm -> False

The empirical-mean comparison follows from argmax with a := model.bestArm:

lean
hcommit_argmax omega model.bestArm :
  empMean omega model.bestArm <= empMean omega (commitArm omega)

This is exactly the RHS comparison written as >=.

5. Regularity contracts

This leaf requires no:

lean
[MeasurableSpace Omega]
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
Measure Omega
IsProbabilityMeasure
Measurable commitArm
Measurable empMean
hbest_gap_pos
spec
reward

It is valid for arbitrary K : Nat; no 0 < K, [NeZero K], Fintype, or DecidableEq contract is needed.

6. Retrieval evidence

Relevant checks:

lean
#check Set.Subset
#check ETC.measurableSet_commitArm_ne_bestArm
#check MeasureTheory.Measure.mono

Mathlib evidence: Measure is defined over Set α -> ENNReal, and the documentation explicitly notes that a measure can be applied to sets without first proving measurability; monotonicity appears as the mono field. 
Lean Community

Local evidence from the newest compiled theorem confirms that the event shape

lean
{omega : Omega | commitArm omega = model.bestArm -> False}

is already accepted in the project and namespace.

7. Classification

Project-local missing leaf.

Not imported, not a port candidate, not a Mathlib candidate, and not theorem-card-only. This is an ABRL-specific event-reduction lemma.

8. Failure policy

If the proof fails:

First try the robust change ... version for the final inequality.

If namespace elaboration fails, place it inside namespace ETC and remove the ETC. prefix.

If Rat order is unavailable, add only the minimal Rat import already used elsewhere, likely:

lean
import Mathlib.Data.Rat.Basic

Do not pivot to Hoeffding, concentration, martingales, filtrations, or the final probability theorem. Also do not add ordered-measurability imports unless this pure subset leaf is already compiled.
