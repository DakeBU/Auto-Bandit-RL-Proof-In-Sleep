The ETC exploration count surface is now sufficient to take one deterministic exploration-only regret consumer. I would consume ETC.exploreArm directly, not define commit behavior or stochastic machinery yet.

Thought for 2m 41s
1. Next single executable leaf

Do the exploration-only deterministic regret scaffold next.

Recommended row:

ETC-EXPLORATION-REGRET-BOUND

Recommended theorem:

lean
ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls

This is now the natural one-step consumer of:

lean
ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound

Do not define the full ETC action trace yet. The existing exploration selector:

lean
ETC.exploreArm spec : Nat -> Fin K

is already a valid action trace for the pure exploration phase.

2. Why this before an exploration-phase boundary?

The count and regret adapters already support the pure exploration horizon:

lean
spec.explorationPulls * K

So the next compiled leaf should prove:

exploration pseudo-regret ≤ (sum of gaps) * explorationPulls

This is the first ETC-specific deterministic regret scaffold, but it does not involve commitment, empirical means, argmax, probability, or concentration.

An explicit “exploration-phase action trace boundary” becomes useful when you introduce a trace with phase switching. That is not needed for this leaf.

3. File placement

Use a new file:

BanditRLProof/Algorithms/ETCRegretLemmas.lean

Then import it from:

lean
BanditRLProof.lean

Reason: this is no longer just a count lemma. It is an ETC-specific regret scaffold consuming the count layer.

4. Imports

Use:

lean
import BanditRLProof.RegretCountBounds
import BanditRLProof.Algorithms.ETCCountLemmas

No new Mathlib import should be needed if the existing files expose the required Rat, Finset, pseudoRegret, and pullCount APIs.

Do not import:

lean
MeasureTheory
ENNReal
Probability
Concentration
Filtration
Empirical mean / argmax machinery
5. Exact Lean-facing statement
lean
import BanditRLProof.RegretCountBounds
import BanditRLProof.Algorithms.ETCCountLemmas

namespace BanditRLProof

theorem ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K) :
    pseudoRegret model (ETC.exploreArm spec) (spec.explorationPulls * K) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) := by
  exact
    pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound
      (model := model)
      (action := ETC.exploreArm spec)
      (n := spec.explorationPulls * K)
      (B := spec.explorationPulls)
      (hB := by
        intro a
        exact le_of_eq
          (ETC.pullCount_exploreArm_explorationPulls_mul_K_eq spec a))

end BanditRLProof
6. Local APIs to use

Use exactly:

lean
pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound
ETC.pullCount_exploreArm_explorationPulls_mul_K_eq

Do not reopen:

lean
pullCount
pseudoRegret
pseudoRegret_eq_finset_sum_gap_mul_pullCount
FiniteBanditModel.gap_nonneg
ETC.pullCount_exploreArm_mul_K_eq
ETC.pullCount_exploreArm_add_K_eq_add_one

Those dependencies are already encapsulated.

7. Regularity contracts

The theorem should require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(model : FiniteBanditModel K)

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
Concentration assumptions
Commit policy assumptions
Empirical mean assumptions

The positivity condition is already inside:

lean
spec.hK : 0 < K

No explicit decidability or finiteness assumptions should be needed.

8. Classification

Classify this as:

ETC-EXPLORATION-REGRET-BOUND:
  project-local compiled ETC deterministic regret scaffold

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
final ETC regret theorem

It is a local executable bridge from round-robin counts to deterministic exploration regret.

9. Failure policy

Use a fail-closed policy.

If this leaf fails:

Confirm the imports:

lean
import BanditRLProof.RegretCountBounds
import BanditRLProof.Algorithms.ETCCountLemmas

If the count bound proof is brittle, replace:

lean
exact le_of_eq
  (ETC.pullCount_exploreArm_explorationPulls_mul_K_eq spec a)

with:

lean
simpa using
  le_of_eq
    (ETC.pullCount_exploreArm_explorationPulls_mul_K_eq spec a)

If theorem namespace resolution is brittle, fully qualify:

lean
BanditRLProof.ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
BanditRLProof.pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound

If the RHS shape does not match, do not rewrite the theorem’s target with a different algebraic orientation. Keep it aligned with:

lean
pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound

Do not define the full ETC trace in this batch.

Do not add empirical means, commit argmax, probability, concentration, filtration, or final ETC regret.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

10. Minimal batch

Complete only:

ETC-EXPLORATION-REGRET-BOUND

with:

BanditRLProof/Algorithms/ETCRegretLemmas.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next review should decide whether to introduce the first phase-switching ETC action trace boundary or keep extending deterministic ETC-only scaffolds.