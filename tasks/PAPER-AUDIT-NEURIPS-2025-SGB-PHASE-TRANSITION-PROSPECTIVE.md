# Prospective SGB phase-transition follow-on audit

Task id: `PAPER-AUDIT-NEURIPS-2025-SGB-PHASE-TRANSITION-PROSPECTIVE`

Kind: `literaturePort`

Status: `activePort`

Harness: `hierarchical`

## Goal

Prospectively audit the two-arm phase-transition evidence in Baudry, Johnson,
Vary, Pike-Burke, and Rebeschini, *Does Stochastic Gradient really succeed
for Bandits?* (NeurIPS 2025).  The core target is the exact `K = 2`
specialization of Theorem 2.  A bounded companion target closes Corollary 1
from the already compiled Theorem 1 without presenting that direct consumer
as independent phase-transition evidence.

## Frozen source and timing

- Source card:
  `PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB`.
- Official camera-ready PDF SHA-256:
  `a3aff97fe2179c47fff61cc51453b84a082332e2a205f7fa2268cc68cba73b3d`.
- Corollary 1: physical PDF p. 5.
- Theorem 2: physical PDF p. 6; full proof in Appendix C, pp. 31--40.
- Machine-readable target freeze:
  `research-wiki/papers/sgb-phase-transition-round13-freeze.json`.
- Timing boundary: the paper was already source-locked and Theorem 1 was
  already compiled.  These exact follow-on targets were frozen on
  2026-08-27 before any target-specific Lean proof file or tactic attempt.
  This is not an independently held-out paper selection.

## Core target: exact two-arm Theorem 2 specialization

Use arm `0` for the source optimal arm and arm `1` for the source suboptimal
arm.  The fixed IID laws are

```text
arm 0: Rad(Delta), with masses (1+Delta)/2 at +1 and (1-Delta)/2 at -1
arm 1: dirac 0
```

Retain `0 < Delta < 1`, source zero initialization, a fixed `eta`, the actual
generated sampled pseudo-regret, and

```text
lambdaDelta = (1/2) * log ((1 + Delta) / (1 - Delta)).
```

If `eta > lambdaDelta`, the frozen endpoint is the `K = 2` reading of the
paper's tilde-Omega conclusion: for every `epsilon > 0`, there exist `c > 0`
and `d : Nat` such that eventually

```text
c * T^(1 - (1 + epsilon) * lambdaDelta / eta) / (log T)^d
  <= expected sampled pseudo-regret at source horizon T.
```

The finite Appendix-C phase construction is the authoritative producer for
this asymptotic form.  The terminal name is frozen as
`twoArmRademacherDirac_theoremTwo_polynomialRegret`.

## Bounded companion: Corollary 1

For source horizon `T >= 2`, set

```text
eta_T = sqrt (log T / T).
```

The finite target uses the exact Theorem-1 right-hand side with its constant
term simplified to `1 / eta_T` when `2 * eta_T * sourceC eta_T <= Delta`, and
uses the pathwise trivial bound `Delta * T` otherwise.  A second theorem gives
an explicit absolute-constant upper bound implying
`O(sqrt(T * log T))`.  The terminal name is frozen as
`twoArmFixedIIDDirac_corollaryOne`.

## Core route, with the original first leaf split at the compiled boundary

The original nth-pull leaf is only partially closed.  Its chronological
stopping/indexing half and its selected-reward-law half now have separate
evidence states:

1. **Compiled:** define the zero-based arm-`0` nth-pull time with `WithTop Nat`
   as the explicit not-yet-pulled value, prove the stopping-time/measurability
   boundary, and identify every finite hit by its exact action and before/after
   pull counts.  The stopped reward and post-pull probability are measurable,
   but have source semantics only under a finite-time witness.
2. **Compiled latent half:** the first `m` coordinates of any fixed latent arm
   have their finite product law; this law lifts through the stream marginal
   of the coupled SGB trajectory; and every finite nth optimal-arm pull reads
   coordinate `(pullIndex, 0)` almost surely.  This is not an IID theorem for
   totalized stopped values or for values conditioned on all pulls occurring.
3. **Blocked native half:** prove that forgetting the latent stream recovers
   the native fixed-IID SGB trajectory law, then transport the latent phase
   event and the source embedded-chain recurrence.  Stream-marginal equality
   plus a.e. reward readout is not trajectory-law equality.
4. Compile Appendix-C Step 1: if the optimal-arm probability after its `n`th
   pull is at most `1/(2*T)`, the conditional probability of no further
   optimal-arm pull over the remaining horizon is at least `1/2`, yielding
   the exact starvation regret charge.
5. Build the `S0`/`S1` phase producer: latent IID reward-block law plus its
   native-process transport, Rademacher anti-concentration, ballot-prefix
   constraint, and the
   deterministic implication into the starvation event.

## First three companion leaves

1. Prove the pathwise and integral bound
   `twoArmSampledPseudoRegret Delta T <= Delta * T`.
2. Show that `2 * eta * sourceC eta <= Delta` implies the Theorem-1 margin
   and simplifies its constant term to at most `1 / eta`.
3. Prove positivity and scalar logarithm/square-root bounds for `eta_T`, then
   assemble the explicit finite and asymptotic Corollary-1 endpoints.

## Hidden contracts

- Theorem 2 retains adaptive selection: the pull-ordered reward blocks must be
  derived from a latent product law and a native trajectory-law adapter, not
  inserted as a selected-reward IID premise.
- Source horizon `T`, chronological time, and optimal-arm pull count are
  distinct indices.
- The not-yet-pulled nth-pull case remains explicit.
- Phase events and stopped values must be measurable.
- Integer ceilings, log domains, parity/path constraints, and eventually-large
  horizon conditions remain explicit.
- The tilde-Omega constants may depend on `eta`, `Delta`, and `epsilon`, but
  not on `T`.
- Corollary 1 uses a horizon-indexed family of fixed-rate policies.  It is not
  a single time-varying policy and is not Proposition 4.

## Nonclaims

This task does not claim general-`K` Theorem 2, Theorem 3, Theorem 4, a
time-varying learning-rate policy, or verification of the external paper.
Corollary 1 is a direct consumer of compiled Theorem 1 and must not be used as
evidence that the polynomial lower-bound route is complete.

## Current verified outcome (2026-08-27)

- `twoArmFixedIIDDirac_corollaryOne_piecewise` and
  `twoArmFixedIIDDirac_corollaryOne` compile for the generated fixed-IID
  two-arm trajectory, actual sampled pseudo-regret, `0 < Delta < 1`, source
  horizon `T >= 2`, and the horizon-indexed fixed rate
  `sqrt (log T / T)`.  The latter uses the explicit absolute constant
  `2 + 1 / log 2 + 2 * exp 2`.
- The Theorem-2 route has one compiled deterministic Appendix-C Step-1
  consumer.  Measurable fixed-cutoff trigger/starvation events carry the exact
  pathwise charge `Delta * (T - n)`, and
  `twoArmFixedIIDStepOneStarvationEvent_charge_mul_probability_le_integral`
  instantiates `charge * P(event) <= expected sampled regret` on the canonical
  generated fixed-IID trajectory measure.
- A separate 24-declaration producer now compiles the zero-based arm-0 nth-pull
  time as a `WithTop Nat`, with `top` as the explicit missing-pull value.  It
  proves the stopping-time and ambient measurability boundary, identifies the
  finite chronological coordinate by exact before/after pull counts and the
  selected action, and makes the stopped reward and post-pull success
  probability measurable.  It assumes no selected-reward IID law.
- A separate seven-declaration latent-reward layer now proves the fixed-arm
  finite product law, lifts it through the coupling's exact stream marginal,
  specializes it to the optimal arm, and proves that every finite nth pull
  reads its corresponding latent coordinate almost surely.  It also compiles
  two normalization leaves for the future native-process adapter.
- The latent coupling's visible trajectory marginal has not yet been proved
  equal to the native fixed-IID SGB trajectory.  Conditional no-return
  probability `>= 1/2`, the Rademacher/ballot phase producer, asymptotic
  assembly, and the frozen Theorem-2 terminal remain uncompiled.  The central
  target therefore remains blocked; the compiled latent product/readout,
  chronological bridge, deterministic consumer, and Corollary 1 are not
  terminal evidence for it.

## Gate

```bash
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditCorollaryOne.lean
lake env lean Tests/StochasticGradientBanditCorollaryOneCanary.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTheoremTwoStarvation.lean
lake env lean Tests/StochasticGradientBanditTheoremTwoStarvationCanary.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTheoremTwoNthPull.lean
lake env lean Tests/StochasticGradientBanditTheoremTwoNthPullCanary.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTheoremTwoLatentReward.lean
lake env lean Tests/StochasticGradientBanditTheoremTwoLatentRewardCanary.lean
python tools/bandit.py check
```

The three Theorem-2-specific files are source-shaped producer/consumer
milestones only; their existence does not promote the frozen terminal.
