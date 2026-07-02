I’ll keep this to one local deterministic leaf and use the new exploration-horizon count before extending post-commit behavior. The next step should be a horizon-local regret scaffold, not probability or empirical-mean work.

Thought for 2m 35s
1. Next single executable leaf

Do the deterministic regret scaffold over the exploration horizon for ETC.actionWithCommit.

Recommended row:

ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND

This is the right next leaf because the count fact is now compiled:

lean
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq

and the deterministic regret adapter is already compiled:

lean
pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound

So the next theorem should simply connect them. Do not start post-exploration increment facts yet; those will need suffix reasoning and commit-arm-specific cases. The exploration-horizon regret scaffold is smaller and immediately checks that the trace/count layer connects to the regret scaffold.

2. Exact Lean-facing statement

Add this theorem to:

BanditRLProof/Algorithms/ETCRegretLemmas.lean

Recommended theorem:

lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K) (commitArm : Fin K) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) := by
  exact
    pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound
      (model := model)
      (action := ETC.actionWithCommit spec commitArm)
      (n := spec.explorationPulls * K)
      (B := spec.explorationPulls)
      (hB := by
        intro a
        exact le_of_eq
          (ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
            (spec := spec)
            (commitArm := commitArm)
            (a := a)))

If le_of_eq orientation is brittle, use:

lean
        exact
          le_of_eq
            (ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
              (spec := spec)
              (commitArm := commitArm)
              (a := a))

or:

lean
        simpa using
          le_of_eq
            (ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
              (spec := spec)
              (commitArm := commitArm)
              (a := a))
3. Imports and local APIs

Update ETCRegretLemmas.lean to import the trace-count layer:

lean
import BanditRLProof.RegretCountBounds
import BanditRLProof.Algorithms.ETCTraceCountLemmas

If the file already imports ETCCountLemmas, that can remain, but the new theorem should directly depend on:

lean
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound

Do not import:

lean
MeasureTheory
ENNReal
Probability
Filtration
Concentration
Empirical mean / argmax files
4. Local APIs to use

Use exactly:

lean
pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq

Do not reopen:

lean
pullCount
pseudoRegret
ETC.actionWithCommit
ETC.actionWithCommit_eq_exploreArm_of_lt
ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le
ETC.pullCount_exploreArm_explorationPulls_mul_K_eq

Those dependencies are already encapsulated.

5. Regularity contracts

The theorem should require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(model : FiniteBanditModel K)
(commitArm : Fin K)

Do not add:

lean
0 < K
Measure
MeasurableSpace
IsProbabilityMeasure
ENNReal
Real
Integrable
Filtration
SubGaussian
Commit correctness assumptions
Empirical mean assumptions
Concentration assumptions

The condition 0 < K is already carried by:

lean
spec.hK : 0 < K

inside ETC.Spec.

6. Classification

Classify this as:

ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND:
  project-local compiled ETC deterministic regret scaffold

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
empirical-mean leaf
final ETC regret theorem

It is a local executable bridge from the fixed-commit trace count theorem to the deterministic regret adapter.

7. Failure policy

Use a fail-closed policy.

If this leaf fails:

Confirm ETCRegretLemmas.lean imports:

lean
import BanditRLProof.RegretCountBounds
import BanditRLProof.Algorithms.ETCTraceCountLemmas

If namespace resolution is brittle, fully qualify:

lean
BanditRLProof.pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound
BanditRLProof.ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq

If the count-bound proof does not elaborate, isolate it:

lean
have hcount :
    forall a : Fin K,
      pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K) <= spec.explorationPulls := by
  intro a
  exact le_of_eq
    (ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
      (spec := spec)
      (commitArm := commitArm)
      (a := a))

then pass:

lean
(hB := hcount)

Do not prove any post-exploration commit-arm count fact in this batch.

Do not add empirical means, commit argmax, probability, concentration, filtration, conditional expectation, or final ETC theorem facts.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

8. Minimal batch

Complete only:

ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND

with:

one theorem in BanditRLProof/Algorithms/ETCRegretLemmas.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next review should decide whether to start the first post-exploration commit-arm count increment lemma or add a generic suffix-count helper.