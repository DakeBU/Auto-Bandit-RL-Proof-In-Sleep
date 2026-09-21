# Causal ordered-law producer

`BanditRLProof/Algorithms/CausalOrderedLaw.lean` constructs a joint PMF by
recursively drawing each node from its conditional table and appending the
draw to its topologically ordered history. Parent indices are strictly earlier
nodes; `GraphModel.local_table` requires the primitive table to depend only on
the declared parents. This is an ordered DAG representation, not a supplied
family of interventional joint distributions.

Proved interfaces:

- `joint_snoc`: actual recursive sampling gives the prefix probability times
  the final conditional probability.
- `joint_factorization`: the constructed joint mass is the product of node
  conditional masses evaluated on the assignment's earlier coordinates.
- `joint_normalized`: total joint probability is one, from the constructed PMF.
- `GraphModel.doModel`: replace intervened tables with point masses and remove
  their incoming parent edges; unchanged tables retain their parent locality.
- `doModel_factorization`: the actual modified joint mass is the product of
  unchanged factors and intervention point-mass factors.
- `intervention_incompatible_zero`: an assignment violating any imposed node
  value has zero probability under the constructed intervention law.

The common node-value type can be any type supported by PMFs; the finite-value
contract will specialize it to a finite type. Heterogeneous node alphabets can
later be encoded with support restrictions or generalized dependent tables.
No heterogeneous encoding or graph-relabeling theorem is claimed here.

The public root imports the module. `Tests/CausalOrderedLawCanary.lean`
instantiates the incompatible-intervention result on three binary nodes and
audits the producer declarations. This structural check is **not** the frozen
noisy recommendation/performance canary. That canary remains mandatory.

Remaining mathematical chain: marginalization of descendants and nonparents,
unchanged reward-parent kernel factorization under non-reward interventions,
finite allocation/coverage, actual repeated sampling and recommendation,
importance moment/bias and Bernstein producers, full simple regret, attained
optimal allocation, and the repaired parallel bridge. No causal-topic endpoint
or independent semantic acceptance follows from this producer milestone.
