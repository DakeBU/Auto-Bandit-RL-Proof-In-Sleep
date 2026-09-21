# Park2026 regret proof: bounded obstruction adjudication

Date: 2026-09-20. Source park26a.pdf SHA256 c192f3345a20227243a822e8fc60d2fd0b8f71d44d5f5f3cc7e35f267d33d102. This adjudicates specific proof implications, not the truth of the intended minimax rate.

## Eq133: an actual counterexample to the claimed process

Use K=2, T=8, any p in (1,2], and iid X_j equal to -1 or 0 with probability 1/2 each. The raw p-moment is nu=1/2. For the exact source cutoff b_s=(nu*s/(2*max(1,log(T/(K*s)))))^(1/p), b_3=(3/4)^(1/p)<1 and b_4=1. Define U_j^(s)=X_j 1{|X_j|<=b_s}-E[X_j 1{|X_j|<=b_s}], as in Eq113-114. Thus every U_j^(3)=0, whereas U_j^(4)=X_j+1/2.

Let c1>0 be any finite claimed p-dependent constant, and M_s=exp(-lambda sum_{j<=s}U_j^(s)-c1*nu*s*lambda^p), the process in Eq133. On the history A={X_1=X_2=X_3=-1}, of probability 1/8, the first three contributions to the s=4 centered sum total -3/2; including X_4+1/2 gives -1+X_4. Therefore

    E[M_4 | F_3]/M_3
      = exp(lambda-(c1/2)*lambda^p)*(1+exp(lambda))/2 > 1

whenever lambda>0 and (c1/2)*lambda^(p-1)<1. Such a lambda exists and can also satisfy any positive common tilt restriction lambda<=1/(2*b_star), since all cutoffs through T are finite and p>1. For example take lambda=min(1/(4*b_star), (1/(2*c1))^(1/(p-1))). Consequently M_s is not a supermartingale for the natural observation filtration. This failure is within the source raw-moment model and its exact common-count threshold, not merely an abstract triangular-array warning. The iid stream can be an arm's sample stream; the argument concerns the asserted prefix process and does not require constructing an algorithm action trace. Even if a particular peeling interval does not contain both 3 and 4, the printed assertion that this process is a supermartingale for s>=0 is false; no replacement maximal proof is supplied here.

Eq132 fixed-prefix MGF control is compatible with this counterexample. A one-time expectation bound does not imply a conditional supermartingale increment inequality. Eq142 therefore cannot be justified by applying Ville to Eq133 as printed. This does not prove Lemma7 or the main regret rate false: an alternative maximal argument may exist.

## Eq285: an explicit failure of the invoked probability implication

Let H take two values with probability 1/2 each. Given H=good let a fresh success event have probability G=1/2; given H=bad let G=1/100. Put E={H=good}. Then P(E)=1/2, P(success|E)=1/2, and

    1/(P(success|E)*P(E))-1 = 3,
    E[1/G-1] = (1+99)/2 = 50.

Thus marginal guarantees of the exact form used in Eq283-284 do not yield Eq285. All conditional probabilities here are strictly positive and below one. The construction can be realized by a conditional Gumbel threshold experiment, since its success probability spans (0,1) as the location varies for a fixed positive scale. It is a counterexample to the probability inference, not a claim that these two history locations are reachable with the exact H-BE estimates and bonuses. Those algorithm-specific restrictions would need their own inverse-tail proof. Replacing G by an unconditional probability changes the interface needed by the conditional arm-decomposition argument.

## Main Theorem5: ordinary logarithm boundary

For K=2, fixed T>=2, nu=1 and a two-arm deterministic instance with means 0 and -Delta, take 0<Delta<=1. Both reward laws satisfy the raw moment bound and the gap is positive. In the displayed expression

    [nu^(1/(p-1))*log(T*Delta^(p/(p-1))/K)+K] / Delta^(1/(p-1)),

the numerator tends to negative infinity as Delta tends to zero. Hence any finite positive multiplicative constant gives a negative proposed upper bound for all sufficiently small Delta, whereas expected pseudo-regret is nonnegative (and initialization incurs a positive gap). This rules out an unrestricted finite-time reading of that displayed expression. A clipped logarithm, explicit large-gap regime, or separate small-gap term changes the theorem; none is silently imported here. If the notation is intended purely asymptotically for fixed instance, this finite-time objection does not refute that different quantified claim. The source does not give a complete uniform regime resolving this boundary.

## Remaining dispositions and external dependencies

The Eq225 random deficit needs a positive part for the subsequent nonnegative tail-integral identity. Eq275-to-276 absorption of nu^(1/(p-1)) into nu^(1/p) is not uniform in arbitrary nu as written; the omitted nu in the small-gap cutoff and nu-dependent c require an explicit normalization argument. Peeling endpoints, rounded-lattice comparison and the peak-crossing cell in Lemma13 are not certified. These are additional reasons not to import the printed complete regret proof; no repair of them is claimed.

The bounded decision is to retain H-BE as distinct known-horizon randomized prior art and reject unqualified import of its printed full regret guarantees. No H-BE theorem is used by the selected BCL endpoint. Accordingly its cited arm-decomposition instantiation, Gumbel-max equivalence, Ville-based chain, lattice lemma and minimax lower-bound references are not accepted dependencies of an ABRL production result. External proofs were not independently certified by reading the local appendix. The separate IPW repair uses its own elementary scalar martingale and Bernoulli MGF arguments; it does not inherit the rejected regret chain, Marcinkiewicz-Zygmund or von Bahr-Esseen as unchecked proof dependencies.

This is a final bounded source-selection disposition rather than an obligation to invent a new H-BE proof. The frozen representative remains BCL. No Lean certification, experiment validation, author-issued correction, or topic completion follows.


Review status and source/artifact hashes are recorded separately in `runs/extended-topics-20260919/park-adjudication-audit.json`. These are mathematical audit documents, not Lean declarations.
