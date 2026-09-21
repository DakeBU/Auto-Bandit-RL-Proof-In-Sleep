# Combinatorial development case: Evaluation and appendix draft

Section insertion for the ICLR evidence package, using the existing case-draft
format. This draft is not inserted into the canonical manuscript or anonymous
snapshot and has not been typeset. The citation key `chen2016combinatorial` is
stored in `ICLR-CASE-REFERENCES.bib` from official JMLR BibTeX; reconcile it with
the manuscript bibliography during integration. Independent review of this
draft is recorded separately in `cucb-case-validation.json`. This is descriptive evidence, not the controlled all-topic
evaluation. The full manuscript and current submission-format checks remain
separate obligations.

## Evaluation insertion

### Reusing probability interfaces while repairing adaptive counting

CUCB combines optimistic arm estimates with an approximation oracle to select
sets of arms under probabilistic feedback. We formalized its refined regret
bound and both polynomial-smoothness bounds from
[Chen et al.](https://jmlr.org/papers/v17/14-298.html), retaining explicit model
and proof differences. This case tests whether a shared library can support
the complete connection between an adaptive policy, its observed samples and
a nonlinear reward guarantee. An estimate based on independent samples would
not establish the required result for the policy's actual observations.

The construction uses one causal infinite trajectory. Each round draws a fresh
oracle action from the current clipped indices and then draws that action's
feedback. Compatible observed marginals connect arm estimates to fixed arm
means, while the signed approximation-regret identity accounts for oracle
failure. Independent source and proof review accepted the complete chain
under its disclosed assumptions, including measurable oracle sampling and the
range condition needed to invert the smoothness modulus.

The central repair concerns the analysis counters. The source rescales a
sampling threshold by trigger probabilities, but its deterministic and random
trigger branches have different coefficients. That rescaling is not a valid
identity across the branches. We instead charge a round to an arm with the
smallest counter normalized by its own threshold coefficient. This changes
the proof's accounting while leaving CUCB's action rule unchanged. Conditional
exponential bounds on the actual action-feedback mixture control insufficient
observations; finite layer-cake counting and a common cutoff then yield the
refined and polynomial endpoints. The proof retains the first charge and the
oracle-failure credit rather than dropping their residual terms.

A compiled export of the 38 production modules identifies 38 direct value-term
reference pairs to 15 project declarations outside those modules, including
generated declarations. Of these pairs, 29 target four files unchanged from
the initial library. Two use a conditional MGF interface introduced during
HOO development, while seven target shared integration and cutoff components
developed with CUCB. The finite instances also reuse a uniform-measure
interface hosted in the Thompson module; this does not transfer Thompson's
regret theory. These distinctions separate existing-library use, cross-topic
development and newly factored mathematics without treating all references as
independent human-written lemmas.

The primary finite instance has noisy arm values, overlapping actions,
probabilistic extra observations and nonlinear product rewards. Its actual
first-round regret is positive, and it instantiates the accepted full bounds.
Additional consumers cover deterministic triggering, a random approximation
oracle and the signed no-bad-action case. Public-root, Tests, full harness and
local publication checks passed. Together, the evidence establishes a
reviewed extension using shared interfaces and an explicit repair of adaptive
accounting. It does not estimate time or tokens saved; controlled comparisons
and the all-topic evidence synthesis remain open.

## Appendix insertion

### Frozen target and statistical construction

The target comprises Algorithm 1 and Theorems 1 and 2 of Chen et al. (2016).
The finite feasible actions have distinct selected subsets. Possible-trigger
sets are nonempty, and untriggerable arms are removed. Arm outcomes lie in
$[0,1]$. For each action, restricting its feedback law to observation of arm
$i$ and then projecting that arm's value gives the observation probability
times a fixed marginal law. This compatibility requirement permits dependence
among arms but excludes arbitrary value-dependent censoring. Total reward is
nonnegative and integrable, with a monotone mean-based score and the stated
smoothness modulus.

The modulus is continuous and strictly increasing on the nonnegative reals,
with $f(0)=0$. Every positive gap $0<d\le\Delta$, where $\Delta$ is the maximum
positive action gap, must lie in its range. Strict increase alone does not
provide this inverse-range property.

The measurable oracle returns an $\alpha$-approximate action with probability
at least $\beta$, for $\alpha,\beta\in(0,1]$. Each call uses fresh randomness
after the current estimates have been formed. With $\mathrm{OPT}$ denoting the
best expected reward, the metric is

$$
R(H)=H\alpha\beta\mathrm{OPT}
      -\mathbb E\!\left[\sum_{t=1}^{H}Y_t\right].
$$

It can be negative. If $d(a)=\alpha\mathrm{OPT}-r(a)$, the exact decomposition
is $R(H)=\mathbb E\sum_{t=1}^{H}d(A_t)-H\alpha(1-\beta)\mathrm{OPT}$.
The final subtraction supplies the oracle-failure credit; replacing this
quantity by ordinary optimal-action regret would change the theorem.

### Repair of threshold accounting

For a positive gap $d$ in the inverse range of the modulus $f$, let
$u=f^{-1}(d)$ and define the source threshold coefficient

$$
c(d,p)=\begin{cases}
6/u^2,&p=1,\\
\max\{12/(u^2p),24/p\},&0<p<1.
\end{cases}
$$

The threshold is $\ell_H(d,p)=\log(H)c(d,p)$. The piecewise definition prevents
using $\ell_H(d,p_i)p_i/p_j=\ell_H(d,p_j)$ across mixed branches. Charging to
an arm minimizing $N_i/c(d,p_i)$ resolves this step: if its normalized count
exceeds $\log H$, every candidate's count exceeds its own threshold. The charge
uses the chosen action and past analysis counters before feedback; it need
not be measurable before the oracle action has been drawn.

Let $C$ indicate such a charge and $Z=C\mathbf1\{i\text{ observed}\}$. For
$\lambda\ge0$, the actual conditional action-feedback mixture satisfies

$$
\mathbb E\left[
 \exp\{(1-e^{-\lambda})p_iC-\lambda Z\}
 \mid\text{past}\right]\le1.
$$

This leads to a charged-observation tail and bounds sufficiently sampled bad
rounds. Distinct integer charges bound the remaining gap costs by a finite
layer-cake integral, including the initial charge. The full refined endpoint
retains each arm's lower-gap threshold term, its integral up to the upper
gap, and the source-qualified summable-tail residual. A common cutoff across
arms gives the two polynomial-smoothness endpoints for $f(u)=\gamma u^\omega$,
$\gamma>0$ and $0<\omega\le1$. The deterministic and random-trigger constants
remain separate, including the latter's additional
$\sum_i (24\log(H)/p_i)\Delta$ term. The performance bounds apply for $H\ge1$.
Horizon zero uses the reward identity; horizon one and empty bad-action families receive explicit
boundary proofs. The separately proved finite-concavity result is not a
dependency of this common-cutoff endpoint.

### Concrete instances and dependency attribution

The primary environment is constructed from 64 equiprobable atoms. Three arms
have Bernoulli means $1/4,1/2,3/4$, and the feasible actions select $\{0,1\}$ or
$\{1,2\}$. Selected arms are observed surely; a fair coin controls observation
of the remaining arm. Product rewards give action means $1/8$ and $3/8$.
An exact oracle chooses the inferior action in the initial tie, giving actual
$R(1)=1/4$. This exercises adaptive learning in a noisy, overlapping-action
model rather than a singleton or zero-regret specialization. Separate
instances prove the deterministic-trigger endpoint, the random-oracle endpoint
with $\beta=1/2$, and a no-bad-action endpoint with $\alpha=1/3$. The random
oracle ignores its input and is only a probability-contract witness.

The dependency export resolves actual module ownership before selecting seeds.
It records 739 owned nodes, 1,673 direct boundary nodes and 44,048 reference
edges. The 38 outward project value-reference pairs comprise 35 value-only
pairs and three also present in declaration types. Generated equations and
instance proofs remain included. The initial-library comparison uses Git file
blobs; introduction commits distinguish the HOO conditional-MGF interface from
the four shared files introduced with CUCB. Counts include production examples
and exclude the six `Tests` modules as seeds. They do not measure proof size,
human effort or algorithmic performance.

Extraction rebuilt the public root and bound the graph, generated exporter and
build log by hash. The production receipt separately records the shared gate
and publication checks. The scripts and evidence paths are documented in
`CUCB-CASE-EVIDENCE.md`; replay requires the pinned Git history and local archive.
Portable packaging, controlled evaluations and final manuscript integration
remain pending.

## Evidence bindings and local writing check

- Mathematical scope: `CUCB-CONTRACT.md`, `CUCB-SOURCE-OBLIGATIONS.md`, full
  reviewed reader and `cucb-semantic-review.json`.
- Counts and provenance: `cucb-case-summary.json` and
  `summarize_cucb_case.py`, pinned to `b79f236`.
- Joint validation: `cucb-production-validation.json`, code/site `7853623`.
- Recent-source failures are documented separately in
  `cmoss-full-source-disposition.json`; this insertion does not import or
  compare unaccepted CMOSS rates.

Local author check: claim/evidence alignment 4/5, confidence high for the
recorded local artifacts; prose clarity 4/5, confidence moderate before
independent review; submission readiness 2/5 because this is an untypeset
section draft with no all-topic controlled evaluation or manuscript join.
Overall stance: suitable for bounded case review, not submission acceptance.
No acceptance probability is inferred from these writing diagnostics.
