# Extended Pro Review After RatCast Nonzero Denominator

## 1. Selected candidate

**Candidate A: `ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION`.**

Now that the denominator chain has reached `Rat` nonzeroness, the next useful leaf is to introduce the **deterministic ETC empirical mean at the exploration horizon**, together with one denominator-rewrite theorem. This is still narrow: no probability space, no stochastic model, no concentration, and no connection to the abstract `Omega -> Fin K -> Rat` wrong-commit consumer yet.

Candidate B is redundant after the compiled nonzero theorem. Candidate C remains premature.

---

## 2. Exact Lean-facing definition and theorem

Use exactly this definition:

```lean
def ETC.empMeanAtExploration
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) : Rat :=
  sumRewards (ETC.actionWithCommit spec commitArm) reward a
      (spec.explorationPulls * K) /
    (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat)
```

Companion theorem:

```lean
theorem ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) :
    ETC.empMeanAtExploration spec commitArm reward a =
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
          (spec.explorationPulls * K) /
        ((spec.explorationPulls : Nat) : Rat) := by
  simp [ETC.empMeanAtExploration,
    ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq]
```

If this is placed inside `namespace ETC`, prefer:

```lean
def empMeanAtExploration
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) : Rat :=
  sumRewards (actionWithCommit spec commitArm) reward a
      (spec.explorationPulls * K) /
    (pullCount (actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat)
```

and:

```lean
theorem empMeanAtExploration_eq_sumRewards_div_explorationPulls
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) :
    empMeanAtExploration spec commitArm reward a =
      sumRewards (actionWithCommit spec commitArm) reward a
          (spec.explorationPulls * K) /
        ((spec.explorationPulls : Nat) : Rat) := by
  simp [empMeanAtExploration,
    pullCount_actionWithCommit_explorationPulls_mul_K_eq]
```

---

## 3. Local APIs / imports

Required local APIs:

```lean
sumRewards
pullCount
RewardTrace
ETC.actionWithCommit
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
```

Likely project import:

```lean
import BanditRLProof.Algorithms.ETCTraceCountLemmas
```

If `sumRewards` / `RewardTrace` are not re-exported through that file, import the trace core file that defines:

```lean
ActionTrace
RewardTrace
pullCount
sumRewards
```

No probability/measurability import should be added.

No concentration or stochastic-process imports should be added.

---

## 4. Intended proof route

The proof is purely definitional plus denominator rewriting.

1. Unfold:

```lean
ETC.empMeanAtExploration
```

The left side becomes:

```lean
sumRewards (ETC.actionWithCommit spec commitArm) reward a
    (spec.explorationPulls * K) /
  (pullCount (ETC.actionWithCommit spec commitArm) a
    (spec.explorationPulls * K) : Rat)
```

2. Rewrite the denominator with:

```lean
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
```

which should reduce:

```lean
pullCount (ETC.actionWithCommit spec commitArm) a
  (spec.explorationPulls * K)
```

to:

```lean
spec.explorationPulls
```

3. Close by `simp`.

A more explicit fallback proof:

```lean
theorem ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) :
    ETC.empMeanAtExploration spec commitArm reward a =
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
          (spec.explorationPulls * K) /
        ((spec.explorationPulls : Nat) : Rat) := by
  unfold ETC.empMeanAtExploration
  rw [ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq]
```

---

## 5. Regularity contracts

Use exactly:

```lean
{K : Nat}
(spec : ETC.Spec K)
(commitArm : Fin K)
(reward : RewardTrace Rat)
(a : Fin K)
```

Do **not** add:

```lean
hexplorationPulls_pos : 0 < spec.explorationPulls
```

for the rewrite theorem. The equality is valid even when `spec.explorationPulls = 0`, because `Rat` division is total and both sides have the same rewritten denominator.

Also avoid:

```lean
[MeasurableSpace Omega]
Measure Omega
Omega -> RewardTrace Rat
Measurable reward
empMean : Omega -> Fin K -> Rat
IsProbabilityMeasure
Independence
SubGaussian
Filtration
ConditionalExpectation
```

This leaf is deterministic only.

---

## 6. Retrieval evidence from Mathlib / local declarations

Local compiled declarations already provide the required denominator identity:

```lean
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
```

The current denominator chain also confirms that the project has the needed future division-side facts:

```lean
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos
ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos
ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero
```

For this leaf, only the exact-count equality is consumed. The positivity and nonzero facts are not needed for definitional unfolding, but they justify why this empirical-mean definition is safe for later algebraic division lemmas under `hexplorationPulls_pos`.

Mathlib side: no specialized theorem is needed beyond ordinary `Rat` division and simplification. The denominator rewrite is project-local.

---

## 7. Status

**Status:** project-local.

This is not imported, not a Mathlib candidate, not a port candidate, and not theorem-card-only. It is the first concrete project-level deterministic empirical-mean API.

---

## 8. Failure policy

If the theorem does not compile, repair only the definitional rewrite.

Recommended sequence:

1. Check the exact equality theorem statement:

```bash
python3 tools/bandit.py list-lean-decls ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq --statement
```

2. If `simp` fails, use explicit unfolding and rewriting:

```lean
  unfold ETC.empMeanAtExploration
  rw [ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq]
```

3. If namespace qualification is the issue, remove `ETC.` inside `namespace ETC`.

4. If cast normalization is brittle, change the RHS denominator to:

```lean
(spec.explorationPulls : Rat)
```

instead of:

```lean
((spec.explorationPulls : Nat) : Rat)
```

These are normally definitionally/simplification equivalent, but the direct cast is often easier.

5. If `RewardTrace Rat` is not in scope, import the local file defining `RewardTrace`.

6. Stop after the definition and one denominator-rewrite theorem compile. Do not add measurability, stochastic reward traces, pairwise concentration, or wrong-commit instantiation in the same batch.

---

## Assessment of the compiled Rat nonzero denominator adapter

The Rat nonzero denominator adapter was a reasonable step before empirical-mean construction. It completed the denominator ladder:

```text
exact exploration pull count
-> Nat positivity
-> Rat positivity
-> Rat nonzero denominator
```

That lets the new empirical-mean definition stay simple and total while preserving a separate, reusable nonzero-denominator contract for future algebraic lemmas.
