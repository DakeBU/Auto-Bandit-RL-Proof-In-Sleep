# Extended Pro Review Response: After ETC Wrong-Commit Probability Design

- Date: 2026-06-30
- Tool/model: ChatGPT Extended Pro
- URL: https://chatgpt.com/c/6a42c911-bf74-83e8-a11c-1b9505119415
- Prompt file: `reports/extended_pro_after_wrong_commit_design_candidate_prompt_2026-06-30.md`
- Local gate before review: `python3 tools\bandit.py check`
- Boundary:
  `ETC-WRONG-COMMIT-PROBABILITY-DESIGN`
- Recorded from raw response:
  `reports/extended_pro_after_wrong_commit_design_raw_response_2026-06-30.txt`

## Reviewer Decision

- Chosen next leaf: ETC-MEAS-COMMITARM-NE-BESTARM
- Classification: project-local missing-leaf
- Status: reviewer-approved

## Exact Lean-Facing Statement

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

## Imports And Local APIs

- `Mathlib.MeasureTheory.MeasurableSpace.Defs` or the smallest existing import exposing `Measurable`, `MeasurableSet.singleton`, and `MeasurableSet.compl`.
- Local model declarations exposing `FiniteBanditModel` and `model.bestArm`.
- Put the theorem in a new probability/measurability-canary file, not in deterministic `ETCTrace`.

## Intended Proof Route

1. Build the equality event `{omega | commitArm omega = model.bestArm}` from `hmeas_commit` and singleton measurability.
2. Take measurable-set complement.
3. Convert the complement to `{omega | commitArm omega = model.bestArm -> False}` by `simpa` or extensional conversion.

## Regularity Contracts

- `[MeasurableSpace Omega]`
- `[MeasurableSpace (Fin K)]`
- `[MeasurableSingletonClass (Fin K)]`
- `hmeas_commit : Measurable commitArm`
- No `Measure`, probability instance, `ETC.Spec`, rewards, empirical means, argmax, gaps, filtration, concentration, or final theorem assumptions.

## Retrieval Evidence

- Local: `FiniteBanditModel`, `FiniteBanditModel.bestArm`.
- Mathlib: `Measurable`, `MeasurableSet.singleton`, `measurableSet_eq`, `MeasurableSet.compl`.
- This follows the local measurable-event canary pattern already used by `measurableSet_actionTrace_eval_eq`.

## Failure Policy

- If the singleton-preimage route fails, try `measurableSet_eq` for the codomain equality event and then preimage through `hmeas_commit`.
- If `simpa [Set.compl_setOf]` fails, use `apply hEq.compl.congr; ext omega; simp`.
- If typeclass inference fails, keep both `[MeasurableSpace (Fin K)]` and `[MeasurableSingletonClass (Fin K)]` explicit.
- Do not proceed to empirical-mean comparison, concentration, or probability bounds in the same batch if this leaf fails.

## Raw Extended Pro Response

I’ll resolve this as a proof-engineering choice, not a probability step. I’ll check the likely Mathlib surface for finite-valued measurability versus ordered comparison measurability, then give one concrete leaf with fallback.

---

1. Pick

Pick Candidate A: ETC.measurableSet_commitArm_ne_bestArm.

Do not start Candidate B yet. Candidate A is the cleanest first compiled canary because it only tests:

measurable finite-valued random variable;

singleton measurability in Fin K;

complement closure of measurable sets.

It does not touch Rat, empirical means, ordered comparisons, finite unions, measures, or probability inequalities.

2. Exact Lean-facing statement

Place it in a new probability/measurability-canary file, not in the deterministic ETCTrace layer.

lean
theorem ETC.measurableSet_commitArm_ne_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (hmeas_commit : Measurable commitArm) :
    MeasurableSet {omega : Omega | commitArm omega = model.bestArm -> False} := by
  have hEq : MeasurableSet {omega : Omega | commitArm omega = model.bestArm} := by
    simpa using
      (hmeas_commit (MeasurableSet.singleton model.bestArm))
  simpa [Set.compl_setOf] using hEq.compl

I would keep the theorem without spec, mu, reward, empMean, or hbest_gap_pos. None of them are used.

3. Local APIs/imports

Minimal Mathlib import:

lean
import Mathlib.MeasureTheory.MeasurableSpace.Defs

Local APIs needed:

lean
FiniteBanditModel K
model.bestArm : Fin K

No local ETC API is needed except the model declaration, so avoid importing the whole deterministic ETC trace file unless that is currently the only module exporting FiniteBanditModel.

Mathlib evidence: Measurable f is defined by measurable preimages; MeasurableSingletonClass supplies measurable singletons and measurableSet_eq; MeasurableSet.compl closes measurable sets under complement. 
Lean Community
+2
Lean Community
+2

4. Intended proof route

Proof route:

Build the equality event:

lean
have hEq : MeasurableSet {omega : Omega | commitArm omega = model.bestArm} := by
  simpa using
    (hmeas_commit (MeasurableSet.singleton model.bestArm))

Take the complement:

lean
simpa [Set.compl_setOf] using hEq.compl

The event

lean
{omega | commitArm omega = model.bestArm -> False}

is just the complement of

lean
{omega | commitArm omega = model.bestArm}

with the negation written in implication-to-False form.

5. Regularity contracts

Required:

lean
[MeasurableSpace Omega]
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
(hmeas_commit : Measurable commitArm)

Not required:

lean
Measure Omega
IsProbabilityMeasure mu
ETC.Spec K
RewardTrace Rat
empMean
hcommit_argmax
hbest_gap_pos
Fintype (Fin K)
DecidableEq (Fin K)
0 < K

0 < K is not needed here; the existence of model.bestArm : Fin K is already part of the local model object.

6. Retrieval evidence

Use these local checks after adding the import:

lean
#check Measurable
#check MeasurableSet.singleton
#check measurableSet_eq
#check MeasurableSet.compl
#check FiniteBanditModel
#check FiniteBanditModel.bestArm

The important Mathlib facts are:

Measurable f unfolds to “preimages of measurable sets are measurable.” 
Lean Community

MeasurableSingletonClass gives singleton measurability, and Mathlib also exposes MeasurableSet.singleton / measurableSet_eq. 
Lean Community

measurable sets are closed under complement via MeasurableSet.compl. 
Lean Community

7. Classification

Project-local missing leaf.

It is not an imported theorem and not worth upstreaming to Mathlib. It is an ETC-facing canary around existing Mathlib primitives.

8. Failure policy

If the proof fails:

First replace the singleton route with the equality-event route:

lean
have hEqCod :
    MeasurableSet {a : Fin K | a = model.bestArm} := by
  simpa using (measurableSet_eq : MeasurableSet {a : Fin K | a = model.bestArm})

have hEq : MeasurableSet {omega : Omega | commitArm omega = model.bestArm} := by
  simpa using hmeas_commit hEqCod

If the final simpa [Set.compl_setOf] fails, use extensional conversion:

lean
apply hEq.compl.congr
ext omega
simp

If typeclass inference fails for Fin K, do not weaken the theorem. Keep:

lean
[MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]

If importing measure theory into the deterministic ETC file is undesirable, create a separate file such as:

lean
BanditRLProof/Algorithms/ETCMeasurability.lean

If this leaf still does not compile, stop and record the exact import/typeclass obstruction. Do not proceed to empirical-mean comparisons or probability bounds in the same batch.
