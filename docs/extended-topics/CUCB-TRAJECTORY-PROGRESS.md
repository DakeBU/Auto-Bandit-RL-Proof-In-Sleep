# CUCB actual trajectory and observed-marginal MGF

2026-09-18. Partial implementation under the full triggered CUCB contract `81a1998`. No performance endpoint or independent semantic acceptance is claimed. Accepted topics remain 0/10.

## Implemented

- `Algorithms/CUCBHistory`: current feedback has a Boolean observation mask, bounded arm outcomes and a separate real reward. `observationCount` and `observationSum` consume exactly past observed coordinates. `empiricalMean` initializes unseen arms at one; observed/unobserved update identities and the [0,1] range are proved. `upperIndex` implements the source clipped confidence index at source round n+1. `oracleInput_causal` and `measurable_oracleInput` establish an actual causal measurable oracle input, not an assumed action sequence.
- `Algorithms/CUCBTrajectory`: `roundKernel` samples an action from the supplied oracle kernel and then that same action's environment kernel. `roundKernel_rectangle` and `roundKernel_action_law` identify its joint and action-marginal laws. `cucbTrajectory` is one infinite compatible trajectory built from those kernels. Its first input is all ones, its first reward/feedback are genuine, and its successor kernel consumes the actual historical input. `cucbTrajectory_initial_law`, `cucbTrajectory_prefix_compProd` and `cucbTrajectory_condDistrib` are derived from the construction.
- `Algorithms/CUCBObservationMGF`: `ObservationCompatible` is a primitive equality of restricted pushforward measures: observing arm i leaves its given marginal outcome law unchanged. From its bounded support, `marginal_subgaussian` derives Hoeffding's MGF. `integrable_observedFactor` and `integral_observedFactor_le_one` then produce the masked one-round exponential bound, including the no-observation contribution. `observedFactor_eq_exp` retains the random observation indicator inside both the centered increment and compensation.
- `Tests/CUCBTrajectoryCanary`: checks that two observed arms update while an unobserved arm retains its initial mean, and that the first oracle input is all ones. Audits causal input, kernel laws and masked MGF declarations. These are local algorithm/probability checks, not the frozen noisy final-performance canary.

The outcome subtype supplies the bounded [0,1] support. It does not impose independence between distinct arm outcomes. The real reward coordinate is deliberately separate and not assumed bounded. The trajectory construction is generic over action types and Markov kernels; the finite feasible-action model, primitive reward/triggering contracts and approximation-success properties must still be assembled and consumed by the final theorem.

## Still required

The one-step masked MGF currently applies to an individual primitive feedback law. It must be integrated over the actual randomized oracle action and iterated over `cucbTrajectory`; an arbitrary per-round conditional-MGF assumption cannot replace that connection. Charged-trigger lower tails, normalized-charge predictability, count-dependent confidence, the actual/mean reward identity, and all remaining source counting/regret steps remain open. Both exact Theorem 1 and Theorem 2 endpoints in CUCB-CONTRACT.md remain mandatory, including mixed and deterministic triggering branches.

Validation of this increment is recorded separately in the source-bound run receipt once the shared gates finish. No controlled ICLR experiment, independent review, merge or deployment is implied by these modules.
