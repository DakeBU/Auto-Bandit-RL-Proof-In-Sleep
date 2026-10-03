# Multi-agent development case: Evaluation and appendix draft

This is one descriptive case for the all-topic ICLR evidence package. It has
not been inserted into the canonical manuscript, typeset or exported
anonymously. Independent statistics/prose review is recorded in the case
validation receipt. Source selection and production semantic acceptance are
separate records. BibTeX keys `rosenski2016musicalchairs` and
`zhou2025syncdv1` are in `ICLR-CASE-REFERENCES.bib`.

## Evaluation insertion

### Completing the learner while testing the limits of library reuse

Multi-player bandits require a connection between local information and joint
performance. In the selected Musical Chairs algorithm of Rosenski, Shamir and
Szlak (2016), players do not know the population. They first use local collision
frequencies to estimate it and collision-free rewards to rank arms. Each then
samples its own retained candidates until a collision-free pull fixes its arm.
A coordination theorem that assumes the correct common candidate set omits
the statistical producer needed by this learner.

Our formalization constructs the complete chain for stationary independent
arm laws supported on [0,1], with separately sensed collisions and a known
positive lower bound on the top-set boundary gap. The actual exploration law
produces simultaneous population and candidate recovery. The learned
continuation kernel then connects the finite coordination occupation bound
to the chronological action/reward process. At every finite horizon H, the
expected aggregate pseudo-regret is bounded by

    min(nH, n min(H,S) + 8n^2 + delta nH).

The actual visible reward process has an unconditional expected-regret bound
with the coarser exploration charge nS. Conditional pseudo-regret and
unconditional realized expectation are kept separate because conditioning on
the reward-dependent exploration event changes reward means. The exploration
budget explicitly changes the source's population-estimation logarithm to pay
for an all-player union; this is a disclosed repair, not literal acceptance of
the printed budget or a disproof of the paper's final theorem.

This case also limits the library-utility claim. A compiled export of the
twelve Musical Chairs modules contains **zero direct proof/value reference
pairs to ABRL project declarations outside those modules**. All twelve files
were absent from the original library snapshot. The case therefore supplies
no positive direct-reference evidence of reuse from the initial ABRL theorem
library. It does contain 902 unique proof/value reference pairs crossing
between its own modules, reaching 145 targets including generated declarations.
These document integration of interfaces developed within this extension;
they do not measure saved work. Mathlib and Lean-core references are reported
separately, rather than credited to ABRL.

A symbolic noisy instance with two players and three Bernoulli arms derives
means 3/4, 1/2 and 1/4, uses the exact repaired exploration duration, and
instantiates the complete visible-regret theorem. Under its actual full sample
law, a specified event combining successful exploration and transient
coordination has probability at least 3/64; the corresponding mean coordination
charge is 5/4. This witnesses a nondegenerate consumer, not an empirical regret
measurement or a positive realized-regret event. Shared compilation, independent
source review, standard-axiom audit and public mapping checks supply separate
evidence of local acceptance.

The result is a complete selected learner extension with explicit source and
probability boundaries, together with a negative result for direct initial-library
reuse. No productivity benefit, comparative optimality, individual fairness,
adversarial robustness or efficiency improvement is inferred.

## Appendix insertion

### Model, correction and endpoint

There are 0<n<K synchronized players with common stationary arm means and fresh
independent rewards/action coins. A player observes its arm, a collision bit
and collision-free reward; a genuine zero reward is distinct from collision.
Only the nth-to-(n+1)th mean gap must be positive; ties within the selected set
are allowed. True n, mean rewards and the proof's good event are not learner
inputs. Fixed tie order, all-collision fallback, zero-count means, rounding and
clamping make the local policy total, including histories where estimation
fails.

For 0<epsilon<gap and 0<delta<1, use exactly

    S = ceil max(16K/epsilon^2 log(4K^2/delta), 50K^2 log(4K/delta)).

The second logarithm differs from the source's log(4/delta). The first is
preserved using the reviewed actual count/reward argument. No necessity claim
for the larger second budget is made. The exploration round convention uses
exactly S observations and handles H<S by the truncated phase charge.

At H>=S, the normalized good-event pseudo-regret bound is nS+8n^2, with a
source-comparison corollary using 2 exp(2)n^2. The unconditional all-horizon
bound retains delta nH; fixing delta does not establish a sublinear bound.
The delta=1/H corollary requires H>=2 and retains failure residual n. The
finite-prefix construction is causal in its stated model; it does not assert
a general conditional-distribution or cross-horizon consistency theorem.

### Evidence provenance and failures

The compiled graph is bound to commit
`4a09e817cabd67f4ffc3b248ff1487ae55f6dea3`; initial-library comparison uses
`eedcda1db4d84f6bd69ec6ee50e174f6cf4056ac`. The twelve-module scope excludes
Tests as seeds but includes generated/private owned constants. Its 660 owned
nodes and 32,683 direct type/value pairs are not counts of mathematical theorems.
The 371 canonical public reading references use a different source-scanner
definition. The 410-name axiom audit includes the promoted production and
test declarations/instances; its name set is different again. Reproduction
commands and exact category counts are in `MULTI-AGENT-CASE-EVIDENCE.md`.

Source audit also documents why a recent alternative is not substituted into
this chain. The complete relevant synchronous proof of SynCD v1 and its DPE
initialization dependency were read and independently reviewed. Literal
schedule, communication and proof-step mismatches prevent accepting its exact
guarantees for transfer. Finite diagnostics test those local assertions only;
they do not disprove every corrected version of SynCD. The accepted bounded
selection disposition retains Musical Chairs and identifies other screened
papers as unreviewed proof inputs.

Integration failures are retained in the acceptance receipt: a first harness
attempt rejected untracked Lean files, and a first site check rejected an
oversized graph search index. Tracking the files and compacting internal shard
paths resolved those failures. Subsequent full harness and site checks passed
without dropping declarations. These are development/validation observations,
not matched formalizer outcomes or measurements of intervention effects.

### Scope of the all-topic claim

The case is descriptive and has no controlled repeats, baseline success rate
or time/token effect estimate. It does not complete the remaining all-topic
evaluation, manuscript integration or final program acceptance. Shared-library
compatibility is established separately from evidence of theorem reuse; this
case deliberately reports their difference.
