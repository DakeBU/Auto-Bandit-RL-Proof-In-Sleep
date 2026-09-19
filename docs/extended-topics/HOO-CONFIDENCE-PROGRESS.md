# HOO trajectory confidence: proved scope and remaining endpoint

Source implementation commit: `e4c3380631ce792da5115330b7968873ccc616d9`.
Frozen performance contract: `LIPSCHITZ-HOO-CONTRACT.md`, commit `47474f9`.
This is a probability milestone in the repaired HOO line, not completion of
Theorem 6, source Lemmas 14–17, or the Lipschitz topic.

For the actual chronological trajectory, let `A_i` be the node selected using
rewards strictly before round `i`. For a fixed node `v`, the library defines

```
I_i(v) = 1{v is a prefix of A_i}
Z_i(v) = I_i(v) (Y_i - integral y d(law A_i))
T_v(n) = sum_{i<n} I_i(v).
```

`sum_regionCount_eq_visits` identifies `T_v(n)` exactly with the count in the
generated algorithm history. `sum_regionNoise_eq_rewardSum_sub_means` identifies
the centered sum with its reward sum minus the sum of the actual selected node
means. These means may vary across visits to a region.

For Markov reward kernels supported on `[0,1]`, the new proofs derive:

* `trajectory_initial_law`: coordinate zero has the first selected node's law.
* `trajectory_region_condMGF`: each compensated successor increment has a
  conditional fixed-tilt MGF bound, using the constructed trajectory's regular
  conditional distribution and predictable node choice.
* `region_compensated_adapted`: chronological increments are strongly adapted
  to the inclusive coordinate filtration.
* `region_noise_visits_tail` and `region_negative_noise_visits_tail`: for
  `a >= 0`, `b > 0`, the event `+/- sum Z_i >= a` and `T_v(n) <= b` has
  probability at most `exp(-2 a^2 / b)`.
* `region_deviation_confidence`: for either sign and `L >= 0`, the event
  `T_v(n) > 0` and `+/- sum Z_i >= sqrt(2 T_v(n) L)` has probability at most
  `n exp(-4L)`. The finite union covers counts `1,...,n`, including `n=0`
  without inventing later visit times.

No independent region samples, finite future visit times, global exponential
integrability, conditional confidence inequalities, or extra first reward are
assumed. Joint-law exponential integrability is proved from the bounded kernels.
The confidence event is measured after `n` rewards and before decision `n`;
the original source's post-round/pre-round index ambiguity is not suppressed.

The implementation consumes the existing
`Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt`
and `ProbabilityUnionBound.measure_biUnion_finset_le`. The new generic
`Concentration.hasCondMGFUpperBoundAt_of_condExp_le` connects an integrable
conditional expectation bound to that fixed-MGF interface. These are source-level
reuse statements; no fresh compiled-reference graph or efficiency effect estimate
is claimed here.

The public canary uses a noisy, node-dependent two-point reward kernel on the
infinite node set and instantiates both eight-round confidence tails for `[false]`.
Its earlier reward-sensitive generated-action checks remain. This is not yet a
complete geometric A1/A2 infinite-arm model witness.

Still required: transfer of the centered confidence bounds to HOO's optimistic
indices using regional means and geometry; optimal-branch existence and path
comparison; expected poor-region visits with corrected indices; packing and the
three-way regret partition; depth optimization and the complete expected-regret
endpoint; full model witness, independent semantic acceptance, shared topic
mapping and all-topic ICLR evaluation. All ten topics remain mandatory.
