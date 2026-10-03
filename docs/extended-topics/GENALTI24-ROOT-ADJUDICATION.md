# Genalti empirical root and algorithm guards: bounded adjudication

Date: 2026-09-20. Mathematical root/guard adjudication with separate repair and source reviews; see the bound receipt for exact verdicts.
Source: Genalti et al., COLT2024, genalti24a.pdf SHA256 65eceb2cd402baa8c7f5b60d273a103fbd181cf6803a4b7f0d2f4092742fe5b6. Eq13 p9; Algorithm1 p12; Proposition9 p24; Algorithm2 p33 and Proposition10 p34.

## Exact deterministic root classification

Let s>=1 and x_1,...,x_s be finite real data; let a>0. For M>0 put
F(M)=sum_j min(x_j^2/M^2,1), m=#{j:x_j!=0}.
Multiplying Eq13 by positive s gives exactly F(M)=a, where a=c log(1/delta). No sampling assumption is needed.

If m=0 then F=0, so no root. If m>0, set r=min_{x_j!=0}|x_j|>0. Every term is continuous and nonincreasing on M>0. For 0<M<=r all nonzero terms equal1, hence F=m. On [r,infinity), F is strictly decreasing: a term with |x_j|=r strictly decreases from1, and every other term is nonincreasing. Also F(M)>0 and F(M)<=sum x_j^2/M^2, so F tends to0.

It follows that:
- a>m: no root, since F<=m.
- a=m>0: roots are exactly (0,r], hence not unique.
- 0<a<m: by continuity, F(r)=m>a and F(B)<a for sufficiently large B; the intermediate value theorem gives a root M*>r, and strict decrease gives uniqueness.

Thus Eq13 has a UNIQUE positive root if and only if 0<a<m. The equality case admits positive roots but no unique estimator. Proposition9 is the sufficient part of this classification. This proof also supplies the needed sign equivalence F(M)>a iff M<M* whenever the strict condition holds.

## Literal Algorithm1 fails at the second paired round

Assume K>=1,T>=4. Round tau=1 assigns infinite indices to all initially unobserved arms and chooses some arm. It plays that arm twice; each of its two datasets then has one sample and its counter N=1. At tau=2 this arm has nonzero count m in {0,1}.

The printed guard is N=0 OR m<=4 log(tau^(-3)). Both disjuncts are false: N=1 and the right-hand threshold is negative while m>=0. Therefore line7 requests a root with a=c log8, c=(1+sqrt2)^2. Since c>1 and log8>1, a>1>=m; no positive root exists. This is pathwise and independent of rewards or tie choices. Other unobserved arms receiving infinity cannot help: the algorithm computes every index before selection.

An admissible concrete environment is K=2 with both rewards deterministically -1, epsilon=1,u=1. Both raw second moments equal1; every discarded signed tail expectation is either -1 or0, so the optimal-arm truncated non-positivity assumption holds. The failure is of execution, not a regret lower bound (all gaps in this witness are zero).

## Correcting only the logarithm sign is still insufficient

Sample representation convention: Eq13 indexes s observations, including repeated values. Accordingly the datasets here are indexed samples/multisets, with one observation appended to EACH dataset per paired pull; both pulls are not counted in the threshold dataset. Algorithm1 writes set union/cardinality informally. If interpreted as mathematical sets that discard duplicates, the deterministic repeated-reward counting argument below does not apply; such deduplication would also change the estimator/sample-count semantics. We make the intended indexed-observation convention explicit rather than silently formalizing set union as append. The literal second-round obstruction above is unaffected by this convention.

Consider changing the printed guard to m<=4 log(tau^3), leaving all other steps unchanged. Let tau>=2 be the FIRST round at which any observed arm enters the root branch. For the entering arm, at the preceding round its nonzero count m_old was at most 4 log((tau-1)^3): if its counter was zero, m_old=0; otherwise, by firstness, the exploration guard held. A paired round adds at most one observation to the threshold dataset, hence
m<=m_old+1<=4 log((tau-1)^3)+1<=4 log(tau^3)+1.
Now c-4=2sqrt2-1>1 and log(tau^3)>=log8>1. Consequently
4 log(tau^3)+1<c log(tau^3)=a.
The first requested root still cannot exist. This argument applies to arbitrary observed rewards and tie choices, for any first request.

Such a request is guaranteed in a finite admissible example. Take the same two deterministic -1 arms and T=1024. If the sign-only version could run through the start of paired round512 without an earlier root request, it would have511 total nonzero threshold observations. One arm has at least256. But 4 log(512^3)=108 log2<108<256, so that arm enters the root branch by round512 at the latest, contradicting the possibility of completing the algorithm. Thus this modification is also demonstrably insufficient, without selecting a convenient unreachable count state.

Elementary log comparisons used above: log2<1 since 2<e; log8>1 since e<3<8. The estimates 2<e<3 follow directly from its power series. No floating-point comparison is required.

## Exact guard repair and retained obligations

With c=(1+sqrt2)^2, replace the exploration condition by
N=0 OR m<=c log(tau^3).
At tau=1, N=0 always holds. Any root branch occurs at tau>=2 and then m>c log(tau^3)>0, exactly the unique-root condition. Conversely, when m<=c log(tau^3), no unique positive root exists (at equality there is a continuum of roots). Thus this is the exact count criterion for the stated unique-root estimator. In integer terms it requires m>=floor(c log(tau^3))+1.

This repairs ROOT well-definedness only. It changes forced-exploration constants from4 to c, requires an exact or certified comparison near equality, and does not establish empirical-variance validity, measurable arm/threshold selection, independence at random counts, odd-horizon actions, concentration constants or regret. In particular the Eq57 power/coefficient issue remains separate. No author-issued erratum or complete repaired algorithm theorem is claimed.

## Doubling solver: exact endpoint and scale obstruction

Under 0<a<m, let M* be the unique root, eta>0, x_h=2^h eta. By the sign equivalence, Algorithm2 stops at
h*=max(0,ceil(log_2(M*/eta))).
It terminates finitely, returns Mbar=x_h*, and Mbar>=M*. If h*>0, the preceding iterate is below M*, so Mbar<2M*. If h*=0, Mbar=eta, with no universal relative upper bound. Hence always
M*<=Mbar<=max(eta,2M*).
When eta<=M*, the source factor2 guarantee follows (at eta=M* the output equals M*). More generally eta<=2M* suffices, but is not automatic for a fixed absolute tolerance.

Concrete counterexample to the unqualified p33 factor2 sentence: s=1,x_1=eta/10,a=1/2 gives M*=sqrt2 eta/10<eta/2. Then Algorithm2 returns eta>2M*. This is Eq13 with any c>0 and delta=exp(-1/(2c)) in (0,1). To stay additionally within the source algorithm's tau>=2 calibration, fix tau=2 and a=c log8, choose an integer s>a, and let all x_j=b>0. The root is b sqrt(s/a). Choose b=eta sqrt(a/s)/10; then M*=eta/10 and the solver returns eta, exceeding2M*. All rewards can instead be -b without altering Eq13, preserving truncated non-positivity and finite raw moments. This is a deterministic solver-input example, not a reachable Algorithm1 history at tau=2.

Proposition10 already states eta<=M*, so this does not refute its qualified factor2 claim. Its real logarithmic step estimate needs ceiling and nonnegative endpoint handling: if on an event M*<=B, then h*<=max(0,ceil(log_2(B/eta))). To turn a high-probability bracket into a conditional-on-existence statement requires separate event accounting; none is supplied here.

## Scope and next formal boundary

This note proves a deterministic root classification, an actual literal execution obstruction, a reachable sign-only repair obstruction, an exact root-guard repair, and qualified numerical-solver bounds. It does not certify the paper's concentration or regret results. It can reuse finite sums and real continuity in the shared Lean project; no new per-paper library or probabilistic assumptions are required for the root interface. No Lean implementation or full-topic completion is claimed by this note. Proposed repair and source correspondence require distinct reviewers.

## Integration boundary

This is a source-adjudication checkpoint, not a production Lean theorem. The source/provenance ledger changes; the Lean Graph, website declarations, teaching route and result badges do not. Functor classification: none-found-with-reason (deterministic root analysis, no certified cross-setting bridge). All ten topics and their ICLR evaluation obligations remain mandatory, with zero completed topics. Existing production finite-supremum results remain separately accepted. No new Lean/site gate, main merge or deployment is claimed.

Evidence: `runs/extended-topics-20260919/genalti-root-audit.json`. The private reviewed derivation is preserved with its own hash; this page reproduces its mathematics and adds this integration boundary.
