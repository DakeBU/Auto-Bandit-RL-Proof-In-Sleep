# Causal development case: Evaluation and appendix draft

This section draft belongs to the all-topic ICLR evidence package. It has not
been inserted into the canonical manuscript, typeset, or exported anonymously.
The official NeurIPS BibTeX entry uses `NIPS2016_b4288d9c` in
`ICLR-CASE-REFERENCES.bib`. The evidence is descriptive; controlled comparisons
and the all-topic evaluation remain outstanding.

## Evaluation insertion

### Reusing concentration while preserving intervention semantics

Causal bandits test whether shared probability interfaces can support a new
observation model without assuming away the connection between interventions
and data. We formalized the known-parent-law algorithm of
[Lattimore et al.](https://proceedings.neurips.cc/paper_files/paper/2016/hash/b4288d9c0ec0a1841b3b3728321e7088-Abstract.html),
with explicit repairs to its displayed analysis. The construction starts with
an ordered finite causal graph. Interventions replace selected conditional
tables, and recursive sampling produces the joint law. Its reward-parent
marginal identifies the importance weights used by the actual learner.
Repeated samples then determine the estimates, a fixed-order maximizing
recommendation and its expected simple regret.

Two interfaces developed during the heavy-tailed work supply the centered
moment-generating-function bound and its independent-sum composition. Causal
sampling supplies their hypotheses: bounded truncated importance observations,
a derived second-moment bound and independence under the constructed sample
law. This reuse transfers probability lemmas, not a heavy-tailed policy or
its regret theorem. A compiled export of the twenty causal modules records
twenty direct proof/value reference pairs to eight project declarations outside
those modules, including generated declarations. Eighteen pairs target files
unchanged from the initial library; two target the later heavy-tailed module.
These are structural observations, not estimates of development effort saved.

The new mathematics connects this shared concentration layer to intervention
design. We prove coverage for uniform allocation, existence of an attained
covered optimal design, and a normalized parallel-graph allocation with cost
at most twice the constructed rarity parameter. An injective change of finite
representation preserves the actual laws, estimator, recommendation and regret,
allowing nodes to have different finite state spaces. Concrete instances expose
boundaries that an endpoint signature would miss: a noisy graph distinguishes
conditional from interventional reward and has exact one-round regret; fair
and deterministic parallel roots have exact design costs two and four.

Independent semantic reviews and the combined Lean, Tests, harness and local
publication checks accepted these bounded results with their stated deltas.
The case demonstrates a complete intervention-to-performance extension using
shared probability interfaces. It does not establish the unknown-graph or
unknown-parent-law setting, compare actual regrets across designs, or estimate
the causal effect of library access on formalization efficiency.

## Appendix insertion

### Frozen model and actual learner

The representative source is the official 2016 main paper and supplement:
Algorithm 2 and Theorem 3, uniform allocation in Proposition 4, and the
parallel bridge in supplement Proposition 8 (arXiv v1 Proposition 9). The
frozen contract requires a finite observed DAG, known reward-parent
intervention laws, a binary reward, a fixed covered allocation, and positive
fixed sampling budget. The implementation also supports a binary reward
readout on a finite reward alphabet. Actions leave the reward node unchanged.
Finite action order and measurable-singleton instances make recommendation
and integration explicit.

For parent law \(P_a\), allocation \(\eta\), and mixture
\(Q=\sum_a\eta_aP_a\), coverage requires \(Q(z)>0\) whenever any
\(P_a(z)>0\). Zero allocation weights are allowed. Define

\[
c(\eta)=\max_a\sum_z\frac{P_a(z)^2}{Q(z)},\qquad
L=\log(2TK),\qquad B=\sqrt{c(\eta)T/L}.
\]

Each round draws an action from \(\eta\), then an assignment from that
action's actual intervened graph law. The estimator averages
\(Y(P_a/Q)\mathbf 1\{P_a/Q\le B\}\), and the recommendation is an actual
empirical maximizer with fixed-order ties. The implementation derives its
mean and second moment, applies the shared centered-MGF and independent-sum
interfaces, and obtains simultaneous confidence without a caller-supplied
tail premise. Integrating the recommendation's regret yields

\[
\mathbb E R_T\le(2\sqrt2+7)\sqrt{c(\eta)L/T}+1/T,
\qquad \mathbb E R_T\le1.
\]

The coefficient retains two confidence errors and one truncation bias. The
failure probability is at most \(1/T\), correcting the printed probability
direction. These are repairs to the displayed proof, not a refutation of
the asymptotic result or a proof that smaller constants are impossible.

### Design and representation results

Uniform allocation covers all supports and has cost at most \(K\). Convexity
and compact covered sublevel arguments construct an attained optimum; the
learner uses that allocation's true cost in its threshold. This is a
mathematical minimizer, not a numerical optimization implementation.

For \(N\ge2\) independent binary roots with known probabilities \(q_i\),
the code constructs the least integer \(r\in[2,N]\) for which
\(\#\{i:\min(q_i,1-q_i)<1/r\}\le r\). Each atomic action with natural
probability strictly below \(1/r\) receives mass \(1/(2r)\); observation
receives the remaining mass \(1-D\). The count bound proves \(D\le1/2\).
The supplement's printed observation weight would make total mass \(3/2\);
the normalized replacement and strict boundary are disclosed and separately
reviewed. Actual product laws give \(P_a\le2rQ\), including deterministic
roots, so coverage and cost at most \(2r\) follow. The graph-parent adapter
preserves cost exactly. Both this allocation and the attained optimum satisfy
the regret bound with \(2r\) on the right, while their thresholds retain their
respective true costs.

The heterogeneous extension first constructs the native dependent joint law.
It then proves a pushforward identity through a finite product encoding.
Parent laws, coverage, cost and the complete product sample law transport
through that encoding; estimates and fixed-order recommendations agree
pathwise. Thus the performance endpoint does not require an externally
supplied codec or replace the native law by an assumed abstract distribution.

### Concrete checks and failure boundaries

The frozen noisy DAG has edges \(X\to W\), \(X\to Y\), \(W\to Y\), with
\(X\sim\mathrm{Bernoulli}(1/2)\), success probabilities \(1/4,3/4\) for
\(W\) given \(X\), and reward probability \((1+X+2W)/5\). Observation,
\(\mathrm{do}(W=0)\) and \(\mathrm{do}(W=1)\) have means
\(1/2,3/10,7/10\). Conditional reward given \(W=1\) is \(3/4\), distinct
from the intervention mean \(7/10\). Observation-only allocation covers all
parent states and has cost \(8/3\). At diagnostic threshold two the two
intervention biases are \(1/5,3/10\); at the actual tuned budget one, the
threshold lies in \((1,4/3)\), the estimates are \((Y,0,0)\), and
observation-first ties give exact expected regret \(1/5\).

The separate two-root parallel checks use a stochastic reward kernel equal
to \(1/4\) or \(3/4\). Fair roots produce an empty strict rare set and exact
cost two. Deterministic zero roots require intervention-created states and
have exact cost four, attaining \(2r\); observation alone is not covering.
Both instantiate the actual all-horizon learner. Their fixed finite order is
not asserted to put observation first. These are local test constructions,
not numerical examples attributed to the paper.

### Structural evidence and reproducibility

The compiled data snapshot is
`296b09127c041670fe552df18d7d6846e8560ae5`; the initial library baseline is
`eedcda1db4d84f6bd69ec6ee50e174f6cf4056ac`. The executable extraction and replay
script is `runs/extended-topics-20260919/summarize_causal_case.py`. Its twenty
seeds are production modules, excluding Tests. A source-target pair counts as
a proof/value reference when it occurs in the value term, including a
canonical type edge marked `also_in_value`. Repeated occurrences do not add
counts. The export includes generated and private auxiliary declarations and
does not expand the transitive Mathlib dependency graph.

Of the twenty external project pairs, five target the fixed-MGF file, twelve
the finite-argmax file, two the heavy-tail fixed-tilt file, and one a generated
argmax congruence declaration whose recorded owner is an RL file. That last
pair is not evidence of RL regret transfer. File-level provenance distinguishes
unchanged files from files absent at the baseline; it does not measure saved
proof effort or count independent hand-written lemmas.

The latest combined validation records 9,032 root build jobs, 9,135 Tests
jobs, and 437 Python tests with seven skips. The parallel packet additionally
audits all 65 new declarations against the standard Lean axioms. The
extraction reruns an incremental root build to bind compiled inputs; it does
not rerun Tests or the full harness. Exact hashes, replay requirements and
limitations are recorded in `causal-case-summary.json` and
`causal-parallel-validation.json`. Controlled runs and efficiency estimates
remain empty, and all-topic completion remains false.
