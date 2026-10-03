# Finite obstruction to the literal printed BCL regret coefficient

Status: complete Lean finite counterexample now compiled, including actual
policy counts, admissible raw moments, product-law expectation and explicit
positive-gap printed-bound negation. Final shared gates/source review recorded
separately in the current contribution receipt. Separate investigator and adversarial source reviewer
verified the frozen published BCL13 Figure1/Lemma1/Theorem1 contract. This rejects
only that exact radius-four signed-reward policy/endpoint, not the paper's other
estimators or its qualitative logarithmic-rate conclusion.

Use two deterministic arms with rewards0 and-1, epsilon=u=1. Raw second moments
are0 and1, the gap is1, and source pseudo-regret is the expected suboptimal count.
Paper round r uses L=2log r and positive prior counts m,n after initialization.
The actual indices are

    I_best = 4sqrt(L/m),
    I_sub = -1+d(L,n)/n+4sqrt(L/n),
    d(L,n)=min(n,ceil(L)-1).

This counts discarded observations j<L. Equality j=L is retained. If n<L,
all negative observations are discarded and I_sub>4. Otherwise d>=L-1.

Take T=2^50, H=log T=50log2, M=32H+5. The literal printed Theorem1 claims
expected suboptimal count<=M. The following proves a UNIVERSAL PATHWISE bound
N_sub(T)>M first, rather than inferring a pathwise cap from an expectation cap.

The elementary bounds 3/5<log2<1 give30<H<50 and M<1605. The lower bound has
a rational integral certificate: the four right-endpoint rectangles for
integral_1^2 dx/x sum to1/5+1/6+1/7+1/8=533/840>3/5.

Fix any maximizing tie execution and suppose its final count N_sub(T)<=M.
At every late-half paper round r=T/2+1,...,T, n<=M and

    m=r-1-n>=T/2-M>320000H,
    2H-2<L<=2H.

The bound on m follows from2^49-1605>16000000>320000H.
Hence I_best<1/100. If n>=L, the suboptimal index satisfies

    I_sub >= -1+(2H-3)/(32H+5)+4sqrt((2H-2)/(32H+5))
          > -1+1/17+24/25 =8/425>1/100.

Here H>30 gives both fractions>1/17; 1/sqrt17>6/25 follows from625>612.
The n<L case already gives I_sub>4. Thus every late-half choice is forced to
be suboptimal, contradicting N_sub(T)<=M because T/2>1605>M.

Every execution therefore satisfies N_sub(T)>=floor(M)+1>M. Under deterministic
ties the count is deterministic. Under randomized ties the count can be random,
but this uniform integer lower bound still yields E[N_sub(T)]>M. The additive5,
initialization and arbitrary maximizing tie rules are retained throughout.

The obstruction is positive bias from deleting negative rewards. It does not
contradict the accepted confidence statements: the bias can remain well within
their valid radius while forcing extra pulls beyond the printed cutoff.

## Current Lean certificate and scope

BanditRLProof/Algorithms/HeavyTailSourceCounterexample.lean implements the exact
source-policy fixed deterministic tie convention. finite_count_obstruction
proves the finite count inequality; kernel_raw_moment proves admissibility;
ae_deterministic identifies the product law almost everywhere with the fixed
reward stream; expected_regret_eq_count connects the actual expected mean regret
to the same count. literal_printed_bound_false negates the exact positive-gap
sum, with the additive5 INSIDE each summand. autoImplicit is disabled so an
accidentally free summation index cannot become a hidden theorem parameter.

The formal log2 certificate uses the lower bounds on log(4/3), log(5/4),
log(6/5):1/4+1/5+1/6=37/60>3/5. This proves the same required inequality as the
four-rectangle mathematical derivation above. No numeric approximation enters
the Lean proof and no2^50-step simulation is executed.

The stronger universal maximizing/randomized-tie argument above remains a
mathematical statement; the Lean certificate instantiates the actual deterministic
SourcePolicy and its probability law. This is sufficient to refute the literal
source-policy claim. It does not assert a counterexample for every paper
estimator or for an independently changed algorithm. The explicit corrected
upper bound already compiled and passed independent review in the separate
SourcePolicy.robust_expected_regret chain.

Remaining heavy-topic obligations concern the recent-source transitive audits,
accepted shared mappings and all-ten ICLR evidence, not missing links in this
finite instantiated counterexample. See the reader and current gate receipt.

Private independent evidence (hashes recorded in the gate receipt):
PRINTED-REGRET-COEFFICIENT-INVESTIGATION.md and
PRINTED-REGRET-COUNTEREXAMPLE-SOURCE-REVIEW.md. The latter corrects the former's
wording about deterministic rewards versus randomized tie counts.
