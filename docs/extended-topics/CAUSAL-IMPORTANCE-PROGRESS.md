# Covered causal importance producer

`CausalImportance.lean` constructs the sampling mixture by PMF bind and proves
its finite real mass formula. `Covers` requires that every positive action mass
has positive mixture mass. Positive allocation on every action implies this
condition, but the public identities only require coverage: zero action weights
remain permitted. The canary accepts identical action laws with all allocation
on one action and rejects distinct point masses when one support is uncovered.

Under coverage, `importance_identity` proves exact change of measure for every
real function on the finite parent space. `ratio_second_moment` identifies the
mixture second moment of P_a/Q with E_a[P_a/Q]. No unsupported mass is lost by
division at zero. Normalization and nonnegativity come from the PMF producer.

The actual statistic `weightedBit` is Y(P_a/Q)1{P_a/Q<=B}, with a binary reward
Y and B>=0. Its pointwise range is [0,B]. `weightedBit_mean` computes its mean
under the actual paired parent/reward PMF. `truncatedMean_add_bias` separates
the negative bias, `truncationBias_nonneg` proves its sign, and
`truncationBias_le` proves beta<=E_a[P_a/Q]/B for B>0 and reward mean<=1.
`weightedBit_second_le` bounds the actual statistic's second moment by the
same importance second moment. These are finite probability calculations,
not supplied tail events or confidence assumptions.

`GraphModel.mixture_parent_joint` connects these distributions to the existing
ordered-DAG construction: sample an actual intervention from eta, sample its
joint law and observe parents/reward; the resulting law is the mixture parent
law followed by the unchanged reward-parent kernel. The target node must not
be intervened upon, as required by the frozen model.

Remaining: finite uniform/design bounds and attained optimum, actual iid
repeated sampling and empirical recommendation, variance/Bernstein and uniform
confidence, source-tuned cutoff and full simple regret, repaired parallel
allocation bridge, and the frozen noisy performance canary. Independent review,
topic acceptance, shared topic mapping and all-topic ICLR evidence are pending.
