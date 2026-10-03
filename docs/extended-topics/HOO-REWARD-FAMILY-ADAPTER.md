# HOO reward-family interface

The independent HOO round trip found that the original terminal API required a
Markov kernel on the entire arm space, while the paper's Section2 specifies
an arm-indexed family of reward laws and a measurable mean. The prototype
`runs/extended-topics-20260919/HOORewardFamily.lean` removes that extra kernel
premise. It is not yet a public-root production integration.

For every arm x, supply a probability measure M_x on real rewards, supported
on [0,1] and with mean f(x). There is no measurability premise on x -> M_x.
The theorem also does not need global measurability of f: its use along the
countable representative range is measurable, so the source measurable-mean
case is included. Original region measurability remains in RegularCovering.
For the actual covering's fixed representative a_v of each binary-word node v,
define the node kernel Q(v)=M_(a_v). Binary words form a countable measurable
space, so this is a measurable Markov kernel for an arbitrary reward family.
The unchanged causal search consumes the actual sequence of rewards, and the
unchanged trajectory construction uses this Q at the selected node.

To reuse the complete existing proof, the adapter equips X internally with
the full sigma algebra. This changes no set, arm, region, representative,
dissimilarity, mean, packing number or near-optimality dimension. All regions
and the reward-family map are measurable on this auxiliary domain. Applying
the existing theorem and reducing definitions yields the original action
function and the node kernel Q in the conclusion. The auxiliary measurable
space does not appear in the returned trajectory law. Lean checks this
transport definitionally; it is not a supplied equality or new probability
oracle. For an existing global kernel, `familyNodeLaw_eq_nodeLaw` is proved by
reflexivity, so the adapter recovers exactly the original trajectory.

The three new endpoints give (i) the complete expected pseudo-regret rate,
(ii) equality of actual and pseudo-regret expectations at every horizon, and
(iii) the complete actual-regret rate. Each rate chooses one positive gamma
before every N>=1 and retains every real exponent above the actual dimension,
the same log(max(N,2)), the same source-permitted fixed choices, and the
already explicit source repairs. No global-law measurability, confidence,
count, final rate or attained-maximizer premise is introduced.

Focused Lean compilation and the three endpoint axiom audits pass with only
propext, Classical.choice and Quot.sound. This result remains a prototype
until public-root/canary integration, reader/registry mapping and the joint
project gate pass. Independent review is recorded in the HOO semantic receipt;
whole Lipschitz topic and all-ten ICLR completion remain separate.


## Production checkpoint (2026-09-20)

The reward-family adapter is now integrated in the public shared library and its new public-root canary passes. Original-chain, prototype, production port and mapping reviews are independently accepted with explicit deltas. Joint root9017, Tests9116,437Python tests7skips and generated-site checks passed at clean code785af09. Nine canonical reading references and an inline mathematical explanation are verified. Receipt: `runs/extended-topics-20260919/hoo-production-validation.json`. Earlier prototype-only/pending-production wording is historical; all-topic ICLR and topic completion remain pending.
