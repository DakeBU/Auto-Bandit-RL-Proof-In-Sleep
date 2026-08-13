# Book Map Chapter 9 Hoeffding UCBVI canonical completion

Task id: `BOOKMAP-CHAPTER-9-HOEFFDING-UCBVI-CANONICAL-COMPLETION`

Kind: `lean`

Status: `partial`

Harness: `hierarchical`

## Goal

Promote Book Map Chapter 9 only after a canonical known-deterministic-reward
Hoeffding UCBVI-CH algorithm and its generated high-probability cumulative
pseudo-regret theorem compile on one adaptive episode process.  This task is a
strict completion gate, not a documentation-only promotion and not a relabeling
of the existing planner, offline-batch, count-martingale, or normalized-average
results.

The maintained public names remain **BanditRLlib** and
*ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for
Bandit and Reinforcement Learning Theory*.

## Source placement

- Route: `ROUTE-RL-UCBVI`.
- Scenario: `SCN-RL-MDP`.
- Sources: `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` and
  `TXT-SLIVKINS-2019-2024`.
- Proof inspirations only: `WEAPON-UCB-OPTIMISM` and
  `WEAPON-TAIL-INEQUALITIES`.
- Retrieval cards: `MLIB-PROBABILITY-KERNEL`,
  `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MARTINGALE-STOCHASTIC`,
  `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-PROBABILITY-VARIANCE`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, and `MLIB-ASYMPTOTICS`.

Cards and weapons place the route; they are not local Lean proof terms.

## Frozen canonical target

Let `H = mdp.horizon`, `S = Fintype.card State`,
`A = Fintype.card Action`, `K = episodes`, `T = K * H`, and

```text
L = log (5 * H * S * A * T / delta).
```

The canonical model has finite nonempty decidable State and Action types,
measurable singletons and the Standard Borel instances required by the kernel
law; `0 < H`, `0 < K`, and `0 < delta <= 1`; a probability initial-state law;
and a known deterministic reward satisfying `0 <= mdp.reward x a <= 1`.

One history-dependent generated source must use only episodes strictly before
episode `k` to form aggregate counts and the empirical transition kernel.  Its
backward update is the UCBVI-CH recurrence

```text
Q[k,h](x,a) = min (Q[k-1,h](x,a)) H
  (reward(x,a) + P_hat[k](x,a)(V[k,h+1])
    + 7 * H * L / sqrt(N[k](x,a))).
```

The implementation must totalize zero counts at the optimistic value `H`, use
an explicit finite measurable argmax/tie break, initialize the previous table
at `H`, and expose every log, square-root and division domain.  Policy,
estimator, confidence event, regret variable, and terminal theorem must all use
that source's exact `AdaptiveEpisodeBatchSource.trajectoryMeasure`.

The frozen terminal failure set is

```text
{trajectory |
  ucbviCHRegretBound mdp K delta <
    cumulativeEpisodePseudoRegret source initialState K trajectory}
```

where the bound is definitionally the Lean spelling of

```text
20 * H * sqrt(H) * L * sqrt(S * A * K)
  + 250 * H^2 * S^2 * A * L^2.
```

The target theorem is

```text
source.trajectoryMeasure (regretFailureSet ...) <= ENNReal.ofReal delta.
```

The compiled namespace and terminal names are
`AdaptiveCumulativeHoeffdingUCBVI.canonicalRegretBound`,
`.cumulativeEpisodePseudoRegret`, `.canonicalFailureEvent`, and
`.recurrentSource_trajectoryMeasure_cumulativeEpisodePseudoRegret_gt_canonicalRegretBound_le`.
The theorem does not accept confidence,
optimism, regret-decomposition, bonus-sum, or the desired terminal inequality
as caller hypotheses.

The expected corollary must prove integrability and retain the bad-event cost:
an admissible explicit surface has the high-probability bound plus
`K * H * delta`.  It may not jump unconditionally from a probability bound to
an expectation statement.

## Canonical completion gates

1. Bellman policy-evaluation, optimality, and finite occupancy foundations.
2. Generated finite-horizon trajectory and episode pseudo-regret semantics.
3. Same-prefix cumulative aggregate visit and transition-count state, exact
   row sums/successor updates, measurability, and zero fallback.
4. Previous-Q clipped recurrent UCBVI-CH planner and measurable argmax policy.
5. Adaptive same-source simultaneous confidence at actual aggregate counts.
6. Good-event Bellman optimism for every generated episode plan.
7. Same-process cumulative episode-regret decomposition.
8. Actual-count clipped-bonus sum and generated-filtration martingale-noise
   bound with explicit `S,A,H,K,L` constants.
9. Frozen high-probability cumulative pseudo-regret terminal.
10. Failure-aware finite expected-regret corollary and integrability.
11. `Tests/BookMapChapterNineCanary.lean` with full-conclusion typed
    applications and a nondegenerate State/Action `Fin 2`, `H >= 2`, `K >= 2`,
    `delta = 1/2` recurrent-source instance.
12. [x] Independent read-only review with no unresolved P0--P3 finding.
13. [x] Focused/root/Tests/SafeVerify/site and final
    `python3 tools/bandit.py check` gates (3699 jobs; 42 tests, one skipped).
14. GitHub PR, Actions, merge, Pages deployment, and live-page verification.

Chapter 9 stays `partial` unless all fourteen gates pass.

## Compiled Lean chain

- [x] Aggregate transition numerator `N_k(x,a,y)` over prior episodes and all
  stages, with `sum_y N_k(x,a,y) = N_k(x,a)`, exact successor update,
  measurability, normalized positive row, and explicit zero-count fallback.
- [x] The recurrent clipped planner, including previous-Q use, initialization,
  zero-count value, score/value/policy measurability, and exact generated-prefix
  source alignment.
- [x] A same-source actual-count confidence producer on the generated filtration,
  followed by the single-episode optimism certificate.

- [x] Generated episode-regret decomposition, actual-count charge summation,
  generated-filtration Bellman-innovation tail, frozen `20/250` terminal, and
  integrable expected-regret consumer with `K*H*delta`.

The confidence node retains singleton p-sensitive Bernstein coordinates and a
normalized optimal-tail value probe proved from the same generated transition
law. The scalar probe is not a caller premise or independent sample, and it is
not falsely claimed to follow from singleton envelopes alone.

## Existing foundation and completed bridge

The existing
`FiniteHorizonAdaptiveCumulativeHoeffdingUCBVI.lean` compiles paired cumulative
state, stage-indexed transition counts, the cross-stage aggregate denominator,
safe log/radius calibration, a generated adaptive source, and exact
source/prefix alignment. The new canonical `recurrentSource` is separate from
that old foundation source: it folds the strict generated prefix into
aggregate transition rows, applies previous-Q clipping, and exposes the frozen
high-probability and failure-aware expectation terminals. Existing offline iid
confidence, reachability-calibrated covers, batch-average consistency, and
caller-supplied coordinate-confidence contracts remain separate dependencies.

## Nonclaims

This gate does not claim Bernstein or variance-aware/minimax UCBVI, stochastic
reward UCBVI, adversarial initial states, PSRL, model-free RL, infinite horizon,
continuous state/action spaces, sharp paper constants beyond this frozen
UCBVI-CH statement, optional stopping, or an anytime theorem.  Those remain
independent extensions after the known-reward Hoeffding gate.

## Failure policy

Do not weaken the terminal, move confidence to an independent sample model,
replace actual counts by a reachability proxy, omit previous-Q clipping,
smuggle any target conclusion into a hypothesis, or promote a theorem card.
On a genuine block, preserve Chapter 9 as `partial` and record the exact Lean
goal, source/measure alignment, attempted APIs, regularity contract, and next
smallest bridge.
