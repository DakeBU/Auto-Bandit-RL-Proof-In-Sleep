# Extended Pro Review Response: After ETC Wrong-Commit Set Inclusion

- Date: 2026-06-30
- Tool/model: ChatGPT Extended Pro
- URL: https://chatgpt.com/c/6a42d3f1-fb60-83ee-beb3-2f320fc01940
- Prompt file: `reports/extended_pro_after_wrong_commit_subset_candidate_prompt_2026-06-30.md`
- Local gate before review: `python3 tools\bandit.py check`
- Boundary:
  `ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT`
- Recorded from raw response:
  `reports/extended_pro_after_wrong_commit_subset_raw_response_2026-06-30.txt`

## Reviewer Decision

- Chosen next leaf: ETC-PROB-WRONG-COMMIT-LE-WRONG-MEAN-EVENTS-OF-SUBSET
- Classification: project-local probability-wrapper missing-leaf
- Status: reviewer-approved

## Exact Lean-Facing Statement

```lean
ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset: measure of wrong-commit event is bounded by measure of existential wrong-mean event using compiled set inclusion
```

## Imports And Local APIs

Mathlib.MeasureTheory.Measure.MeasureSpaceDef; BanditRLProof.Algorithms.ETCMeasurability

## Intended Proof Route

derive hsubset from ETC.wrong_commit_subset_exists_empMean_ge_bestArm; close with mu.mono / Measure.mono

## Regularity Contracts

mu : Measure Omega, model, commitArm, empMean, explicit hcommit_argmax; no probability instance, no event measurability, no empirical-mean measurability, no concentration

## Retrieval Evidence

local compiled subset lemma; Mathlib Measure.mono / mu.mono

## Failure Policy

only repair measure monotonicity namespace/import or ge_iff_le normalization; do not pivot to empirical-mean measurability, finite unions, concentration, filtration, or final theorem

## Raw Extended Pro Response

## 1. Pick

**A.** Close the measure wrapper now.

This is the correct next leaf because the compiled subset lemma already has exactly the set inclusion needed for the wrong-commit probability bridge. Candidate B/C are regularity infrastructure; useful later, but they do not close the current theorem-card target. Candidate D is unnecessary unless the local import graph unexpectedly fails.

---

## 2. Exact Lean statement

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
        empMean omega a >= empMean omega model.bestArm} := by
  exact mu.mono
    (ETC.wrong_commit_subset_exists_empMean_ge_bestArm
      model commitArm empMean hcommit_argmax)
```

If this theorem is placed **inside `namespace ETC`**, use the unqualified local theorem name:

```lean
  exact mu.mono
    (wrong_commit_subset_exists_empMean_ge_bestArm
      model commitArm empMean hcommit_argmax)
```

---

## 3. Imports / local APIs

Use the existing local API:

```lean
ETC.wrong_commit_subset_exists_empMean_ge_bestArm
```

and mathlib’s measure monotonicity projection:

```lean
mu.mono
-- equivalent route, depending namespace/import exposure:
-- Measure.mono mu
-- MeasureTheory.Measure.mono mu
```

Minimum import posture:

```lean
import BanditRLProof.Algorithms.ETCMeasurability
```

if adding the wrapper outside the file where the subset lemma lives.

If `Measure` or `mu.mono` is not already exposed by the current import chain, the minimal mathlib route is:

```lean
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
open MeasureTheory
```

Mathlib’s current documentation supports this route: measures can be applied to arbitrary sets without first proving measurability, and the `Measure` structure exposes monotonicity from set inclusion to measure inequality. ([Lean Community][1])

---

## 4. Proof route

Let

```lean
S = {omega : Omega | commitArm omega = model.bestArm -> False}
T = {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm}
```

The already-compiled theorem gives:

```lean
S ⊆ T
```

under `hcommit_argmax`.

Then apply measure monotonicity:

```lean
mu.mono : S ⊆ T -> mu S <= mu T
```

No `simp`, no `rw`, no `by_cases`, no finite union decomposition, and no measurability proof should be required.

A more elaboration-stable proof is:

```lean
by
  have hsubset :
      Set.Subset
        {omega : Omega | commitArm omega = model.bestArm -> False}
        {omega : Omega |
          exists a : Fin K, (a = model.bestArm -> False) /\
            empMean omega a >= empMean omega model.bestArm} :=
    ETC.wrong_commit_subset_exists_empMean_ge_bestArm
      model commitArm empMean hcommit_argmax
  exact mu.mono hsubset
```

---

## 5. Regularity contracts and assumptions to avoid

Do **not** add:

```lean
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
hmeas_commit
hmeas_empMean
MeasurableSet ...
IsProbabilityMeasure mu
FiniteMeasure mu
Fintype (Fin K)
DecidableEq (Fin K)
```

Also avoid rewriting the event into `commitArm omega ≠ model.bestArm` unless necessary. The compiled subset lemma uses:

```lean
commitArm omega = model.bestArm -> False
```

so preserving that shape maximizes definitional matching.

Key point: Candidate A is a **measure inequality over arbitrary sets**. It is not a regularity lemma. Measurability of either event is not part of this leaf.

---

## 6. Retrieval evidence

The decisive local evidence is the prompt-provided compiled lemma:

```lean
ETC.wrong_commit_subset_exists_empMean_ge_bestArm
```

Its conclusion is syntactically the exact subset needed by Candidate A.

The official mathlib API evidence is that `Measure` has monotonicity:

```lean
mono {s₁ s₂ : Set α} : s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
```

and measure evaluation is available on sets without separately supplying a measurability witness. ([Lean Community][1])

I also searched the accessible File Library for the ABRL / `ETCMeasurability` identifiers and found no relevant Lean artifact. The retrieved files were unrelated manuscripts/PDFs, so they should not be used as evidence for this proof choice.

---

## 7. Classification

**Leaf type:** probability-bridge wrapper.

**Risk:** very low.

**Dependencies:** only the compiled subset lemma plus measure monotonicity.

**Not included:** empirical-mean comparison measurability, finite existential measurability, Hoeffding, concentration, martingales, filtration, UCB/TS/EXP3/Tsallis/OFUL/RL, or final theorem work.

**Expected compile behavior:** one-line proof should compile if namespace and import exposure are correct.

---

## 8. Failure policy

If the one-line proof fails, do not switch to B/C/D. Apply only local repair:

1. Replace dot projection:

```lean
exact Measure.mono mu hsubset
```

or, if needed:

```lean
exact MeasureTheory.Measure.mono mu hsubset
```

2. If inside `namespace ETC`, remove the `ETC.` qualifier from the subset theorem.

3. If elaboration fails on the set terms, introduce `hsubset` explicitly with the full `Set.Subset` type and then apply:

```lean
exact mu.mono hsubset
```

4. If the failure is only notation normalization around `>=`, try:

```lean
simpa only [ge_iff_le] using mu.mono hsubset
```

5. If `Measure` is not in scope, add/import-route to `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`.

Stop after those repairs and report the first remaining Lean error. Do not add new regularity assumptions or start Candidate B/C infrastructure under this leaf.

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.html "Mathlib.MeasureTheory.Measure.MeasureSpaceDef"
