# Genalti AdaR-UCB: complete qualified positive-regret reconstruction

Date: 2026-09-20. Complete qualified mathematical reconstruction; separate source and mathematical review evidence is bound in the receipt.
Source: Genalti et al., COLT2024, genalti24a.pdf SHA256 65eceb2cd402baa8c7f5b60d273a103fbd181cf6803a4b7f0d2f4092742fe5b6; Algorithm1 p12, Lemma1 Eq11 p9 / appendix Lemma2 p23, Theorem7 Eq19 pp28–31 and Theorem8 pp31–32.
Prerequisites are the independently reviewed deterministic root classification, root concentration, split-mean concentration and adaptive-prefix proofs in the same review directory. The proof below closes the additional variance/index, counting and regret steps. It does not accept the literal original guard or numerical constants.

## 1. Explicit algorithm/model contract

There are K>=2 stationary real reward laws nu_i, independent iid reward streams, common p in (1,2], finite u>=0, and integral |x|^p dnu_i<=u. Each paired selection observes two conditionally independent fresh rewards of its chosen law; realize these as two independent indexed iid streams per arm, retaining multiplicity. All arm streams may be taken independent. Means mu_i exist. Fix an optimal arm star satisfying integral x*1_{|x|>M} dnu_star<=0 for EVERY M>0. Let Delta_i=mu_star-mu_i>=0 and q_i=nu_i(X!=0).

Physical horizon T>=2 has H=floor(T/2) paired rounds. At paired round t=1,...,H use L_t=log(t^3), c=(1+sqrt2)^2. With n=N_i(t-1) previous paired pulls and m_i the nonzero count of the threshold stream prefix, assign index +infinity when n=0 OR m_i<=c L_t. This explicitly replaces the source's incorrect guard; it has no unknown p,u input. Otherwise take the UNIQUE positive root of sum_{j<=n} min((X'_{i,j})^2/M^2,1)=cL_t and define
 muhat_i=(1/n)sum_{j<=n} X_{i,j}1_{|X_{i,j}|<=Mhat_i},
 V_i=(1/(n-1))sum_{j<=n}(X_{i,j}1_{|X_{i,j}|<=Mhat_i}-muhat_i)^2,
 B_i=muhat_i+sqrt(2 V_i L_t/n)+10 Mhat_i L_t/n.
Choose the smallest-index maximizer and observe the next reward from each of the two selected streams. For odd physical T, make one final pull of a fixed arm, say arm1. This endpoint convention fills a source omission and adds an explicit residual; any measurable final-arm choice has the same residual bound below.

At t=1 all n=0. Every finite-index branch has t>=2 and n>=m_i>c log8>1, so n>=2 and sample variance is defined. The corrected guard and root classification ensure a positive finite root. The root's rational strict level sets are measurable; truncation and sample variance are Borel, and finite-arm smallest-index maximization among real/+infinity indices is measurable. Induction on the finite horizon gives a causal measurable paired policy: no future coordinate is read to choose an arm. This is a mathematical implementation argument, not a Lean or floating-point implementation.

If u=0, all rewards and gaps are zero almost surely, so regret is zero; root branches need not occur. Below take u>0. Raw moments imply |mu_i|<=u^(1/p), hence gaps<=2u^(1/p). Assumption on the optimal discarded tail implies mu_star<=0: as M decreases to0, dominated convergence with integrable |X| makes the discarded expectation tend to EX. Therefore every suboptimal arm has mu_i<0 and necessarily q_i>0. No division by q_i=0 is made for a suboptimal arm.

## 2. Sample-variance concentration from independent random pairings

For fixed deterministic M>0 let Y_j=X_j1_{|X_j|<=M}, j=1,...,n, be iid, n>=2, mean mu_M, variance sigma_M^2. Define unbiased V_n=(1/(n-1))sum(Y_j-Ybar)^2. The algebraic identity is
 V_n=(1/binom(n,2))sum_{j<k}(Y_j-Y_k)^2/2.
Set m=floor(n/2)>=1 and h=2M^2. For a uniform permutation pi of n indices, let
 W_pi=(1/m)sum_{r=1}^m (Y_{pi(2r-1)}-Y_{pi(2r)})^2/2.
For every DATA vector, averaging over permutations gives E_pi W_pi=V_n: each unordered pair has the same chance to occupy a paired slot. For each fixed permutation, the m pair terms are independent, lie in[0,h], and each has expectation sigma_M^2. The unused observation when n is odd changes none of these statements.

Convexity of exp (valid for any real exponential parameter) and averaging over permutations yield the centered MGF
 E exp(lambda*(m/h)*(V_n-sigma_M^2))
 <=exp((m*sigma_M^2/h)*(exp(lambda)-1-lambda)), for all real lambda.
This is the same Poisson-type bound already derived for independent bounded sums, although V_n itself is not a sum of independent pair terms. Jensen is applied before averaging over data; finite permutation sums can be interchanged with expectation. Boundedness ensures all integrals exist.

The already derived two square-root deviation bounds therefore give, for every L>0, each with failure<=exp(-L),
 sigma_M<=sqrt(V_n)+2M sqrt(L/m),
 sqrt(V_n)<=sigma_M+2M sqrt(L/m).
Zero variance is handled directly: all iid Y_j are constant almost surely, so V_n=0. Since n/m<=3 for n>=2, either error term is at most2sqrt3 M sqrt(L/n). No Maurer self-bounding theorem is assumed here.

## 3. Empirical index optimism, retaining source bonus10

For centered Y_j-mu_M, absolute value is at most2M and variance is sigma_M^2. The direct bounded MGF argument already derived gives the lower mean deviation with failure<=delta=exp(-L):
 mu_M-Ybar<=sqrt(2sigma_M^2 L/n)+2ML/(3n).
Combine it with the LOWER sample-standard-deviation bound, failure<=delta. Then, outside probability2delta,
 mu_M-Ybar<=sqrt(2V_n L/n)+[2sqrt(2n/m)+2/3]ML/n
             <=sqrt(2V_n L/n)+10ML/n.
The coefficient comparison follows from n/m<=3 and 2sqrt6+2/3<10. On the optimal arm, discarded-tail non-positivity gives mu_star<=mu_M for every M>0. Thus the empirical index is optimistic at fixed n and deterministic M with failure<=2delta.

For random Mhat computed from the independent threshold sample, condition on that sample and apply the deterministic-M estimate to the other sample; integrate on its root event. Do not assert unconditional independence of commonly thresholded observations. On the no-root branch the algorithm assigns +infinity and is automatically optimistic. A union over fixed n=1,...,t-1, followed by substitution of the actual adaptive count, gives
 P(B_star(t)<mu_star)<=2(t-1)/t^3, t>=2.
For n=1 the root event is empty; n=0 gives +infinity. At t=1 optimism is automatic. Equality B_star=mu_star is GOOD; a failure is the strict underestimation event.

## 4. Suboptimal index upper bound on a shared good event

At fixed n>=2, t>=2, use the same root-good event from the accepted Theorem5 reconstruction:
 Mhat<=B=(un/L_t)^(1/p), tail(Mhat)<=(1+2sqrt2)^2 L_t/n.
Its intersection with root existence fails with probability<=2delta_t. Reuse this ONE event below. Conditional on the threshold sample, a one-sided upper-mean MGF tail costs delta_t and yields, by the reviewed Holder bias argument,
 muhat_i-mu_i<=C u^(1/p)(L_t/n)^q,
 where q=(p-1)/p and C=4/3+3sqrt2.
Only one signed mean tail is needed, so its cost is delta_t, not the two-sided2delta_t. Separately the UPPER sample-standard-deviation event costs delta_t, and sigma_M^2<=E Y^2<=u M^(2-p). Let A=u^(1/p)(L_t/n)^q. On these three good conditions,
 sqrt(2V_i L_t/n)<=sqrt2 A+2sqrt(2n/m) A<= (sqrt2+2sqrt6)A,
 10 Mhat L_t/n<=10A.
Hence
 B_i<=mu_i+D A, D=34/3+4sqrt2+2sqrt6<22.
For an elementary strict check, sqrt2<10/7 and sqrt6<49/20 give D<34/3+40/7+49/10=4609/210<22.
The combined suboptimal failure event on its root-existence branch has probability<=4delta_t: rootbad2delta_t, one upper mean tail delta_t, one upper variance tail delta_t. It never requires independence among these events. Union over n<=t-1 gives<=4(t-1)/t^3 for the actual adaptive prefix.

## 5. Corrected count threshold and optimistic selections

Let L_H=log(H^3)>=0. For each Delta_i>0 define
 A_i=L_H*(22*u^(1/p)/Delta_i)^(1/q).
If t<=H, the selected suboptimal arm i is in its finite-index branch, its prior count n>=A_i, and neither its index-upper failure nor the optimal optimism failure occurs, then
 B_i<=mu_i+D u^(1/p)(L_t/n)^q<mu_i+Delta_i=mu_star<=B_star.
For H=1 no finite-index selection occurs. For H>=2 the displayed implication uses L_t<=L_H and D<22; n>=A_i guarantees u^(1/p)(L_t/n)^q<=Delta_i/22. Strictness excludes a tie with the optimal arm. If the optimal arm has an infinite index, selecting a finite-index suboptimal arm is already impossible.

Thus every finite-index selection of arm i either has prior count n<A_i or occurs in a bad round. Prior counts of successive selections of one arm are distinct nonnegative integers, so the number with n<A_i is at most ceil(A_i), regardless of interspersed exploration. The expectation of bad selected rounds for this FIXED arm is at most
 sum_{t=2}^H 6(t-1)/t^3 <=6 sum_{t=2}^H 1/t^2<=6.
This combines the fixed optimal arm and fixed suboptimal arm prefix unions; no random-selected-arm K factor is silently removed. The bound is per arm and will be summed over arms in regret. Consequently expected finite-index selections of i are at most ceil(A_i)+6.

The source's count conversion used coefficient20 without raising it to1/q. Our source-facing correction is explicit: A_i contains22^(1/q) and the updated index analysis; no original coefficient120 or46 is inherited.

## 6. Forced exploration: integer successes, without assuming a selected subsequence is iid

Put b_H=c L_H and r_H=floor(b_H)+1>=1. For a fixed suboptimal arm i, let W_i be the number of observations in its INFINITE original threshold stream needed to see r_H nonzero observations. Since q_i>0, E W_i=r_H/q_i. One direct derivation: waiting times between successive successes have P(G>k)=(1-q_i)^k for k>=0; summing this geometric series gives E G=1/q_i. Independence of disjoint Bernoulli stream blocks gives the same expectation for each of the r_H waits and additivity gives the displayed result. This is a property of the original iid stream, not a conditional assertion about adaptively selected exploration samples.

Every exploration selection occurs while the current nonzero count is<=cL_t<=b_H (the n=0 case has count0). Once r_H successes have been observed, no further exploration selection of that arm can occur by horizon H. Pathwise its exploration-selection count is therefore at most W_i and at most H, even if optimistic selections contributed some successes before W_i. Hence
 E N_i^FE(H)<=min(H,r_H/q_i).
The strict integer crossing r_H=floor(cL_H)+1 is essential, including H=1. This replaces the source's unrounded4L_H/q_i. It does not condition on root existence or assume the adaptively chosen exploration subsequence is independent.

## 7. Complete qualified expected-regret bound

The expected pseudo-regret of the mathematical algorithm above, including the optional last physical pull, satisfies
 R_T <= 2 sum_{i:Delta_i>0} Delta_i*[ceil(A_i)+min(H,r_H/q_i)+6]
        +2u^(1/p)*1_{T odd}.
Every paired choice costs exactly2Delta_i in expected pseudo-regret. The final residual follows from the raw-moment gap cap for the chosen last arm. Each policy/action is causal and the finite regret random variable is bounded by2T u^(1/p), so all expectations used above exist. If u=0 the regret is zero separately. T=0,1 can be handled directly by no paired rounds and the same one-pull cap; the theorem here takes T>=2 as in the source.

This is an actual corrected algorithm-to-expected-performance chain, not a consumer assuming its confidence conclusions. All relevant probability producers are derived in this note and its reviewed prerequisites. The guard, coefficient, ceiling, finite-horizon and endpoint differences are explicit. This is NOT the literal printed Algorithm1/Theorem7.

For completeness, a gap-independent learning term follows for H>=2,u>0. Since ceil(A_i)<=A_i+1, define the remaining additive term
 Q=2 sum_{i:Delta_i>0} Delta_i*[min(H,r_H/q_i)+7]+2u^(1/p)*1_{T odd}.
For every Delta>0, bound paired regret from gaps<=Delta by2HDelta and use the large-gap count bound on the others. This gives
 R_T<=2HDelta+2K L_H 22^(1/q)u^(1/(p-1))Delta^(-1/(p-1))+Q.
Choose Delta=[K L_H 22^(1/q)u^(1/(p-1))/H]^q. The two displayed learning terms are equal, yielding
 R_T<=88 (K L_H)^q (uH)^(1/p)+Q.
For H=1 the direct instance bound applies. This retains a q_i-dependent exploration residual, as the source does; it is not a uniform minimax theorem over all nonzero masses. It does not certify the source constant46 or its unchanged algorithm.

## 8. Source comparison and boundaries

The official COLT2009 Maurer–Pontil PDF was acquired from https://www.learningtheory.org/colt2009/papers/012.pdf, SHA256 4b06ea7eb3a832347df493948deb06a7053aa36d22eba6793d2a4e48ab3935c1. Its Theorems4,10,11 and their local proofs were inspected as a comparison route. The general self-bounding Theorem7 refers onward to Maurer2006; that external proof is not claimed audited here. Our paired-average MGF proof supplies the needed variance estimates directly, so the present regret proof does not depend on that unaudited theorem. Scaling its Theorem10 from[0,1] to[-M,M] introduces width2M; one must not import the source Eq58 coefficient without checking that scaling. No claim is made that the smaller Eq58 event is itself false under every possible sharper argument.

The new result is a mathematically reviewed candidate repair only after separate source and repair reviewers accept it. It is not an author-issued erratum, a Lean theorem, floating-point implementation, main merge, deployment or whole-topic completion. The negative/adaptivity lower theorems and full-paper acceptance remain separate. The frozen primary heavy-tail Lean target remains BCL, not replaced by this unknown-parameter algorithm.

## Publication and validation boundary

Evidence receipt: `runs/extended-topics-20260919/genalti-corrected-regret-audit.json`. It binds the original private proof and separate reviewers, its prior concentration/root dependencies, and the comparison-source PDF. The publication copy changes status wording and adds this boundary; the mathematical derivation remains the reviewed one.

No production Lean declaration, canary, root import, registry node, result badge or compiled dependency edge is added by this document. Source/provenance and the all-topic ledger are updated; Lean Graph and site remain unchanged. Functor classification: none-found-with-reason for this checkpoint (the probability mechanism is not a compiled cross-topic bridge). No new Lean/site gate, main merge, deployment or controlled experiment is claimed. Full-topic acceptance and all-ten ICLR evidence remain outstanding.
