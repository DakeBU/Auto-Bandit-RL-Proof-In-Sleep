# Heterogeneous finite-node representation bridge

Required by the unchanged frozen causal contract and the v2 independent review.
The accepted common-alphabet result is not a substitute for this bridge.

Route: define genuinely dependent node tables and a recursively sampled joint
PMF on `(i : Fin n) -> V i`. Reuse the same topological order and dependent
`Fin.snoc`; do not define the source joint merely by decoding the target law.
Give each node an encoding into a common W and a left-inverse decoder.
The encoded table decodes its past and maps the source draw through the node
encoding. Prove by induction that the encoded joint is the pushforward of the
source joint. This proves valid support and decoding preservation.

Then prove replacement of a typed node table by a point mass commutes with
encoding. Preserve the parent graph, derive encoded parent observations, and
transport the importance statistic, allocation cost, fixed-order recommendation
and expected regret. For finite nonempty node types construct the encoders into
a concrete finite common alphabet; do not assume the common alphabet exists as
an extra source premise. Reward decoding must agree with the binary source node.

Reuse search: CausalOrderedLaw/MarginalLaw already provide homogeneous joint
factorization and intervention marginals; no dependent-node representation is
present. Mathlib Fin.snoc is already dependent and PMF map/bind laws support the
induction. This is a route-local adaptation, not another Lean project or a new
probability library. Actual performance transport and independent review remain
mandatory after the structural identities compile.

## Current implementation and scope (2026-09-20)

The four-module transport packet now constructs native dependent node laws,
the finite product codec, intervention and parent pushforwards, exact importance
cost preservation, the actual product sample-law pushforward, and pathwise
estimator/recommendation/regret identities. The native expected-regret theorem
constructs its codec internally. Uniform and attained optimal native allocations
instantiate the same learner. Independent blind and source reviews accepted this
packet with explicit deltas; the representation objection is resolved.

The additional CausalHeterogeneousLaw module proves native joint and intervention
factorization directly. Tests.CausalHeterogeneousCanary uses a three-valued root
and a two-valued noisy reward, proves actual intervention means 5/12, 1/4, 3/4,
and instantiates the uniform all-positive-horizon rate. Its focused build passes
3608 jobs; printed endpoint axioms are only propext, Classical.choice and
Quot.sound. This supplemental packet has independent blind/source acceptance with explicit deltas; see causal-heterogeneous-review.json for bound hashes.

The reward interface is a binary readout; arbitrary real rewards are not claimed.
The known inputs used by the estimator are parent marginals, not the unknown
reward mechanism. No separate native information-access type system is claimed.
The explicit constant repair and residual 1/T remain unchanged. Parallel design,
the original noisy canary's concentrated cost/bias/conditional/T=1/uncovered
diagnostics, remaining source audit and ICLR evidence remain mandatory. The
global ten-topic Goal and the causal topic remain incomplete.
