# Reward-parent marginalization producer

`CausalMarginalLaw.lean` continues the actual ordered-DAG PMF construction.
It proves that projecting the joint law onto any initial segment gives the
joint law constructed from precisely those conditional tables. Thus later
nodes are summed out, even if the selected reward node is not a sink.

`GraphModel.parentTable` constructs the conditional table from a parent-only
assignment by filling other coordinates with a default value. The graph's
primitive locality condition proves agreement with the original table on
every full history. The default therefore does not change the represented
conditional law. The common value type has an inhabitant for this extension;
the frozen finite nonempty binary model satisfies this requirement.

`GraphModel.parentLaw` is the pushforward of the **actual modified full joint
law**, not a supplied parent distribution. For any target node i untouched
by the intervention, `intervention_parent_joint` proves that the pushforward
onto (parents of i, value at i) is obtained by drawing from this parent law
and then the original parent-only conditional table. Its point-mass version,
`intervention_parent_mass`, proves

    P_a(Z=z,Y=y) = P_a(Z=z) * r(z)(y).

The intervention may alter earlier or later nodes and their induced parent
distribution. Only the target node's own table must remain untouched. The
construction includes arbitrary declared parent sets and does not assume
that every earlier node is a parent. No statistical conditional probability
on a null event is used; the identity holds at zero-mass parent assignments.

The structural canary uses a three-node binary graph with target node one,
an intervention at node zero, and a later node to eliminate. It audits the
producer chain. It is not the frozen noisy performance canary, which remains
open along with coverage/allocation, importance-estimator moments and bias,
actual repeated sampling/recommendation, Bernstein, full regret and design
optimization. Independent semantic review and all-topic ICLR evaluation are
also still pending.
