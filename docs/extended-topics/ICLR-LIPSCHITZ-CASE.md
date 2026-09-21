# Lipschitz development case: Evaluation and appendix draft

Working section insertion for the ICLR evidence package. This descriptive case
uses accepted local mathematics and historical validation, with no controlled
efficiency experiment. It does not modify the canonical manuscript or anonymous
snapshot. The full ten-topic Evaluation remains incomplete. The source citation
`bubeck2011x` is stored in `ICLR-CASE-REFERENCES.bib`, obtained from official JMLR
metadata; manuscript insertion must reconcile this key with the manuscript's
existing bibliography. This Markdown draft has not been typeset or checked
against current submission page limits.

## Evaluation insertion

### Preserving an adaptive algorithm across proof interfaces

We developed the expected-regret guarantee for hierarchical optimistic
optimization (HOO), an infinite-arm bandit policy that refines a binary covering
tree using observed rewards. The selected target is Algorithm 1 and Theorem 6
of [X-Armed Bandits](https://jmlr.org/papers/v12/bubeck11a.html), with explicit
initialization, indexing and endpoint conventions. Its difficulty lies in
connecting the actual adaptive search to geometric packing and concentration:
samples within a selected region cannot be replaced by an independent fixed
sample, and the optimal mean need not be attained by any arm.

The formal chain starts from bounded stationary reward laws and the source's
covering and weak Lipschitz assumptions. It constructs one causal infinite
reward trajectory, derives conditional concentration for the regions visited
by the policy, bounds poor-region visits, and partitions the policy's pseudo-regret into
three disjoint contributions. A packing bound from the near-optimality
dimension then controls the geometric sums. For each exponent above that
dimension, the final theorem supplies a single environment-dependent constant
valid at every positive horizon. Equality of expected realized regret and
expected pseudo-regret is proved under the same trajectory law.

Independent semantic reconstruction exposed an interface restriction that
compilation had not detected. The original endpoint required a measurable
reward kernel on the entire arm space, whereas the source model specifies an
arm-indexed family of reward laws and a measurable mean. HOO uses one fixed
representative per tree node. Since the nodes are countable, the family
restricted to these representatives defines a measurable node kernel without
global measurability of the family. A compiled adapter uses this observation
to reuse the existing regret proof while preserving the actual action function,
geometry and trajectory law. Separate reconstruction, source comparison and
repair review accepted the resulting interface with its explicit source deltas.

The historical 28-module export contains 36 direct proof-reference pairs from
HOO-owned declarations to 21 project targets outside those modules. Git
comparison attributes 28 pairs to five files unchanged from the initial
library and eight pairs to four files introduced later in the program.
Generated declarations are included in these counts. The evidence demonstrates
concrete use of shared interfaces and an accepted repair of their assumption
boundary; it does not estimate development time saved. The later reward-family
adapter is outside this historical graph and has separate acceptance evidence.

A public-root canary instantiates the new family endpoint on infinitely many
binary-sequence arms with distinct means and non-Dirac rewards. Its proved
dimension bound yields a conservative regret exponent, so the canary exercises
the complete chain without asserting sharpness. The recorded production gate
passed the shared Lean root, Tests, full harness and site checks. Together these
artifacts support a descriptive account of source-faithful extension and reuse.
Controlled comparisons and the all-topic evidence synthesis remain pending.

## Appendix insertion

### Mathematical target and source deltas

Let a nonempty arm space carry the source's measurable binary covering. At
depth $h$, regions have dissimilarity diameter at most $\nu_1\rho^h$ and contain
pairwise disjoint open balls of radius $\nu_2\rho^h$, where $\nu_1,\nu_2>0$ and
$0<\rho<1$. The nonnegative dissimilarity vanishes on the diagonal; symmetry
and a triangle inequality are not imposed. Write $f^*=\sup_x f(x)$. The weak
Lipschitz condition is

$$
f^*-f(y)\le f^*-f(x)+\max\{f^*-f(x),\ell(x,y)\}.
$$

For each arm $x$, the probability law $M_x$ is supported on $[0,1]$ and has
mean $f(x)$. The final family interface quantifies over these laws without
assuming measurability of $x\mapsto M_x$. It also does not require global
measurability of $f$, since the proof uses its countable representative range;
the source's measurable-mean case is included. The regular covering retains
region measurability. No compactness or attained optimum is assumed.

Let $d_0$ be the actual near-optimality dimension at the source parameter
$4\nu_1/\nu_2$, defined from contained-whole-ball packing through a nonnegative
extended-real limsup, with $\log 0=-\infty$. For every real $d>d_0$, the theorem
provides $\gamma>0$ such that for all natural $N\ge1$,

$$
\mathbb E\!\left[\sum_{n=0}^{N-1}(f^*-Y_n)\right]
=\mathbb E\!\left[\sum_{n=0}^{N-1}(f^*-f(X_n))\right]
\le \gamma N^{(d+1)/(d+2)}
       \bigl(\log\max\{N,2\}\bigr)^{1/(d+2)}.
$$

Here $X_n$ is selected by the formalized HOO search from rewards strictly
before round $n$, and $Y_n$ has the actual selected representative's law.
The policy and infinite trajectory law are fixed before varying $N$; the
constant is chosen before the universal horizon quantifier. Confidence,
expected visits and the final rate are derived, not endpoint assumptions.
The expectation identity separately holds for every natural horizon under
weaker assumptions, without the dimension or weak Lipschitz condition.

The source and the accepted theorem are kept distinct. The implementation
corrects the right-child depth in Equation 2, initializes both root children
with infinite indices, and makes the post-history selection convention
explicit. It replaces $\log N$ by $\log\max\{N,2\}$ to cover horizon one,
where the unmodified displayed rate would be zero. The empty-packing logarithm
is explicit. Fixed representatives and deterministic left ties instantiate
choices permitted by the source. These differences, including the complete
repaired Appendix A.1 chain, have independent source and repair review.

### Why the reward-family adapter preserves the algorithm

For a node $v$ with fixed representative $a_v$, define $Q(v)=M_{a_v}$.
Countability of the binary-word node space makes $Q$ measurable. Internally,
the adapter equips the arm space with its full sigma algebra and applies the
existing kernel theorem. This transport changes no underlying arm, region,
representative, dissimilarity, packing set or dimension. Reducing definitions
returns precisely the original action and the trajectory generated by $Q$.
For an input that already is a global kernel, equality with the original node
kernel is proved by reflexivity. Thus the repair removes an interface premise
without supplying a new confidence event or replacing the adaptive process.

The public module `BanditRLProof/Algorithms/HOORewardFamily.lean` exposes
`expected_pseudoRegret_rate_family`, `expected_actual_eq_pseudoRegret_family`
and `expected_actualRegret_rate_family`. Its canary invokes the new final-rate
endpoint on the infinite-arm noisy model. A proved dimension bound $d_0\le2$
allows $d=3$, giving $N^{4/5}(\log\max\{N,2\})^{1/5}$. This is not a claim
that the model's dimension equals two or that this exponent is optimal.
A second generic canary accepts an arbitrary reward family with the required
means and support; it exposes no global family-measurability premise. No
concrete nonmeasurable-family counterexample is claimed by these canaries.

### Reuse extraction and validation

The initial library is pinned at `eedcda1`, the compiled graph at `0378d46`,
and production validation at `785af09`. The raw export has 506 seeds, 1,576
boundary nodes and 25,765 edges. One generated seed resolves to an owner
outside HOO, leaving 505 HOO-owned nodes. Removing its outgoing project
reference changes the raw count of 37 pairs to 36, with 21 targets unchanged.
The historical artifact is retained alongside this attribution correction.

Proof edges are selected by `kind=value OR also_in_value=true`. Module owner,
rather than namespace, determines whether a declaration belongs to HOO. Five
target files are byte-identical to their initial-base versions; four are absent
at that base. The [evidence-method note](HOO-CASE-EVIDENCE.md) supplies the full
file breakdown and replay command. These are direct declaration relations,
including generated targets, not independent samples or a productivity metric.

Production validation records 9,017 shared-root build jobs, 9,116 Tests jobs,
437 Python tests with seven skips, and passing site checks. The three family
endpoints have axiom closures containing only `propext`, `Classical.choice`
and `Quot.sound`. Nine reading references bind their statements and owning
modules to the reviewed artifacts. Build jobs include shared dependencies and
are not counts of newly proved theorems. The present statistics replay checks
recorded bytes and Git provenance; it does not rerun these historical gates.

### Evidence boundaries and artifacts

The recent-source comparison is recorded separately in
[Log-Li source disposition](LOGLI-SOURCE-DISPOSITION.md). Its bounded proof and
model objections motivate non-import of that comparison result; they neither
prove impossibility of a repaired asymptotic rate nor enter the selected HOO
proof as assumptions. This case establishes the frozen repaired HOO endpoint,
not every theorem of the primary paper or every Lipschitz bandit result.

The replay depends on the archived graph, Git history and recorded working-file
bytes. Raw Windows hashes and normalized Git content hashes are reported
separately. A portable anonymous release remains to be assembled. No controlled
run, success-rate estimate or causal efficiency effect is reported. Completion
of all ten topics still requires the common evaluation protocol, its required
runs, manuscript synthesis and final integrated acceptance.

Evidence locations relative to the repository root:

- `runs/extended-topics-20260919/hoo-production-review.json` and
  `hoo-production-validation.json`: semantic and production acceptance.
- `runs/extended-topics-20260919/hoo-compiled-references.json`: immutable
  historical graph binding and raw counts.
- `runs/extended-topics-20260919/summarize_lipschitz_case.py` and
  `lipschitz-case-summary.json`: replay and corrected provenance statistics.
- `docs/extended-topics/HOO-SOURCE-OBLIGATIONS.md` and
  `HOO-REWARD-FAMILY-ADAPTER.md`: proof-chain locations and assumption transport.
- `Tests/HOORewardFamilyCanary.lean`: concrete final-rate and generic-family
  interface consumers.
