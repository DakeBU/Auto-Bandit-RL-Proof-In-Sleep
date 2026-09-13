# Proof obligations: Orabona v10 OGD

Task id: `ONLINE-OGD-CH2-FIXED`
Source/signature: `docs/contracts/online-ogd-v1/contract.md`.
Status: accepted-local; PR delivery recorded separately.

| Node | Depends on | Exact public interface | Evidence / status |
|---|---|---|---|
| projection existence and feasibility | mathlib Hilbert projection | project_spec | focused compiled |
| projection identity/uniqueness | variational minimizer condition | project_eq_of_variational | focused compiled |
| source Proposition 2.11 | projection | proposition_2_11 | focused compiled |
| convex differentiable producer | affine secant and gradient derivative | first_order | focused compiled |
| source Lemma 2.12, BOTH inequalities | projection + first_order | lemma_2_12 | focused compiled |
| Algorithm 2.1 constant-step construction | project/step/iterate | iterate_mem, iterate_prefix | focused compiled |
| source Theorem 2.13 constant step | actual trajectory + one-step + finite telescope | theorem_2_13_fixed | focused compiled, residual retained |
| source Eq. (2.1) | fixed theorem + norm bounds + sqrt tuning | equation_2_1_distance, equation_2_1 | focused compiled |
| public nondegenerate instance | all producers and terminals | Tests.OnlineGradientDescent.nondegenerate_canary | public-root compiled, positive regret and residual |
| global validation | root, Tests, export, Python suite | tools/bandit.py check | passed: exit 0, 422 tests, 7 skipped |
| semantic review and source mapping | frozen contract + current bodies + canonical registry | reviewer decision / Book checks | passed: 04_reviewer.md and site/registry receipts |
| PR delivery | code, evidence, all gates | open reviewable PR | delivery receipt after PR creation |

## Failure record

| Attempt | Classification | Observation | Repair |
|---|---|---|---|
| 01 | local Lean lemma gap | final division tactic used a mismatched orientation | keep scaled telescope and normalize by positive multiplication |
| 02-03 | local Lean lemma gap | old/ambiguous multiplication lemma and underconstrained calc target | explicit multiplier and explicit final expression; no header change |
| canary 01 | local Lean lemma gap | loss partial application did not unfold in simp; affine differentiability API mismatch | typed gradient_losses and explicit real inner-product conversion |
| metadata | semantic interface gap in verifier arguments | source_assumption field expects literal header text, not card path | preserve original fence; corrected metadata; same original hashes |
| Book tests 01 | stale test assumption | previous tests hard-coded ten chapters and all non-bandit Books planned | assert current chapter count and exact scoped OGD canonical membership |
| site preview 01 | local schema gap | teaching preview accepts at most four highlighted declarations | show four main steps; projection remains in source theorem and extended highlight inventory |

Reusable leaves: projection and convex-linearization mathematics. Algorithm and
Book wrappers remain project-local. No external unbuilt theorem is promoted.
The initial dependency frontier has moved through all mathematical terminals;
complete local validation and semantic acceptance passed; final PR delivery is recorded separately.
