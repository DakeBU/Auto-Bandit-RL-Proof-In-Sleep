I’ll keep this at the ETC deterministic layer and recommend one named exploration-horizon count fact that directly consumes the compiled multiple-cycle theorem, without defining commit behavior.

Thought for 1m 56s
1. Next single executable leaf

Do the spec.explorationPulls * K specialization next.

Recommended row:

ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT

Recommended theorem:

lean
theorem ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a (spec.explorationPulls * K) =
      spec.explorationPulls

This is the right next leaf because it turns the generic multiple-cycle theorem into the exact exploration-phase count shape that later ETC scaffolds will consume.

Do not define the full ETC action trace yet. The project should first make the exploration-only boundary fully reusable.

2. File placement

Add it to the existing file:

BanditRLProof/Algorithms/ETCCountLemmas.lean

It belongs next to:

lean
ETC.pullCount_exploreArm_mul_K_eq

Do not put it in Algorithms/ETC.lean; this is a count theorem, not a primitive selector theorem.

3. Exact Lean-facing statement and proof
lean
namespace BanditRLProof

theorem ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a (spec.explorationPulls * K) =
      spec.explorationPulls := by
  simpa using
    ETC.pullCount_exploreArm_mul_K_eq
      (spec := spec)
      (a := a)
      (m := spec.explorationPulls)

end BanditRLProof

This should be a one-line specialization. Do not prove it by induction again.

4. Imports and local APIs

No new imports should be needed if added to ETCCountLemmas.lean.

The only local API to reuse is:

lean
ETC.pullCount_exploreArm_mul_K_eq

Do not reuse or reopen:

lean
pullCount_succ
ETC.pullCount_exploreArm_add_K_eq_add_one
ETC.pullCount_exploreArm_K_eq_one
pullCount_eq_finset_filter_card
pseudoRegret
RegretCountBounds
Expectation*

The point of this leaf is to stabilize the public ETC exploration horizon.

5. Regularity contracts

The theorem should require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(a : Fin K)

Do not add:

lean
0 < K
DecidableEq (Fin K)
Fintype (Fin K)
Measure
MeasurableSpace
Rat
ENNReal
pseudoRegret
concentration assumptions

The positivity proof is already inside:

lean
spec.hK : 0 < K

and no explicit decidability/finiteness assumption is needed.

6. Classification

Classify this as:

ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT:
  project-local compiled ETC deterministic count adapter

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
ETC final regret theorem

It is a project-local executable lemma supporting:

round_robin_exploration_counts
pull_count_bound_after_commit
ETC deterministic regret skeleton
7. Failure policy

Use a fail-closed policy.

If this leaf fails:

Confirm it is placed after:

lean
ETC.pullCount_exploreArm_mul_K_eq

If namespace inference is brittle, fully qualify:

lean
BanditRLProof.ETC.pullCount_exploreArm_mul_K_eq

If named-argument elaboration fails, use positional application:

lean
simpa using
  ETC.pullCount_exploreArm_mul_K_eq spec a spec.explorationPulls

Do not reprove the theorem by induction.

Do not define the full ETC action trace in this batch.

Do not start empirical means, commit argmax, probability, concentration, or final ETC regret work.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

8. Minimal batch

Complete only:

ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT

with:

one theorem in BanditRLProof/Algorithms/ETCCountLemmas.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next review should decide whether to introduce the first exploration-phase action-trace boundary or prove a deterministic regret scaffold specialized to the exploration-only ETC trace.