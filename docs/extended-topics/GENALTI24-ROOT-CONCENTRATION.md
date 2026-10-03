# Genalti Theorem5: event semantics and complete bounded-root concentration

Date: 2026-09-20. Mathematical reconstruction with separate source and repair reviews; see the bound receipt.
Source: Genalti et al. COLT2024, pinned genalti24a.pdf SHA256 65eceb2cd402baa8c7f5b60d273a103fbd181cf6803a4b7f0d2f4092742fe5b6. Theorem5 Eq16 pp9–10; proof pp24–26, Eq34–50. The root classification is separately reviewed in genalti-root-adjudication.md (f9883be3306ae5e57a0ad7d4226899d7bb958b4fdebd98839b2f835450194ca3).

## Exact contract and root random variable

Let X_1,...,X_s be independent identically distributed REAL observations, indexed with multiplicity; s>=1, p in (1,2], c>2, delta in (0,1/2), L=log(1/delta)>0, and E|X_1|^p<=u with finite u>=0. Put a=cL and
F(M)=sum_j min(X_j^2/M^2,1), for M>0,
E={sum_j 1_{X_j!=0}>a}.
On E, let Mhat be the unique positive solution F(Mhat)=a. Extend Mhat=0 on E-complement solely to define a measurable random variable; no algorithmic threshold is prescribed there. The finite-data classification gives
E intersect {Mhat>r}=E intersect {F(r)>a} for every r>0.
E is measurable and F(r) is measurable, so these identities at positive rational r prove measurability of the extension. At r=0 the event is E, and at r<0 it is the whole space.

The precise theorem to prove is
P(E intersect {Mhat>B OR tail(Mhat)>beta})<=2delta,
where tail(m)=P(|X_1|>m) under the single-observation law,
B=(us/((sqrt(c)-sqrt(2))^2 L))^(1/p),
beta=(sqrt(c)+sqrt(2))^2 L/s.
Equivalently P(E implies [Mhat<=B and tail(Mhat)<=beta])>=1-2delta. This preserves Eq16's constants on the root-existence event. It is NOT P(bounds | E)>=1-2delta. If u=0, all observations vanish almost surely and P(E)=0, so the theorem is vacuous; hence the substantive proof takes u>0. The function tail is monotone, hence Borel measurable, so the failure event is well-defined. Equality in the root-count criterion is not included in E: roots then exist but are nonunique.

## Fixed-threshold concentration from elementary independent MGFs

For independent Y_j in [0,1], let Z=sum Y_j and mu=EZ. For every real lambda,
E exp(lambda Y_j)<=1+EY_j*(exp(lambda)-1),
by convexity of exp on the unit interval. Independence and 1+x<=exp(x) give
E exp(lambda(Z-mu))<=exp(mu*(exp(lambda)-1-lambda)).
All variables here are bounded, so every exponential expectation exists.

For lambda>=0, exp(-lambda)-1+lambda<=lambda^2/2; Chernoff at lambda=t/mu gives, when mu>0 and t>0,
P(mu-Z>=t)<=exp(-t^2/(2mu)).
For 0<lambda<3, the power-series comparison k!>=2*3^(k-2), k>=2, gives
exp(lambda)-1-lambda<=lambda^2/(2(1-lambda/3)).
Chernoff at lambda=t/(mu+t/3) gives
P(Z-mu>=t)<=exp(-t^2/(2(mu+t/3))).
The chosen lambda is in (0,3) when mu>0. Therefore, for L>0,
P(mu-Z>=sqrt(2mu L))<=exp(-L),
P(Z-mu>=sqrt(2mu L)+(2/3)L)<=exp(-L).
For the upper bound, expanding t^2-2L(mu+t/3) at t=sqrt(2mu L)+(2/3)L gives (2/3)L sqrt(2mu L)>=0. When mu=0, Z=0 almost surely and the square-root deviation conclusions below follow directly; do not substitute lambda=t/mu.

Consequently each of the following STRICT failure events has probability at most delta=exp(-L):
 sqrt(mu)-sqrt(Z)>sqrt(2L),
 sqrt(Z)-sqrt(mu)>sqrt(2L).
For the first, mu-Z=(sqrt(mu)-sqrt(Z))(sqrt(mu)+sqrt(Z))>sqrt(2mu L). For the second, Z-mu>2sqrt(2mu L)+2L, which exceeds the upper-tail threshold just proved. No union over a random M or assumption of independence after adaptive stopping is used.

## Upper root bound: use a deterministic moment threshold

For M>0 and p in (1,2], min(x^2/M^2,1)<=|x|^p/M^p. Thus
mu_B=EF(B)<=su/B^p=(sqrt(c)-sqrt(2))^2 L.
The definition B>0 ensures this equality and the valid moment bound. On E intersect {Mhat>B}, root monotonicity gives F(B)>a. Hence
sqrt(F(B))-sqrt(mu_B)>sqrt(cL)-(sqrt(c)-sqrt(2))*sqrt(L)=sqrt(2L).
Apply the fixed-threshold upper-tail inequality at deterministic B. This proves P(E intersect {Mhat>B})<=delta. It avoids assuming a population bracket root exists and keeps the exact source coefficient.

## Tail bound: split off the missing population-root boundary

Write q=P(X_1!=0). If q<=beta, then tail(M)<=q<=beta for every M>=0, so there is no tail failure on E. This includes beta>=1.

Suppose q>beta. Define g(M)=E min(X_1^2/M^2,1) for M>0. Dominated convergence gives continuity of g on (0,infinity), limit q at M down to0 and limit0 at infinity. Since 0<beta<q, the intermediate value theorem provides a deterministic M0>0 with g(M0)=beta. This is an existence argument, not uniqueness, and M0 is chosen from the fixed observation law, not from data.

On E intersect {Mhat<M0}, root monotonicity gives F(M0)<a. Since mu_0=s beta=(sqrt(c)+sqrt(2))^2 L,
sqrt(mu_0)-sqrt(F(M0))>sqrt(2L).
The fixed-threshold lower-tail inequality therefore bounds this event by delta.
On its complement within E, Mhat>=M0 and
tail(Mhat)<=tail(M0)<=E min(X_1^2/M0^2,1)=beta.
Thus P(E intersect {tail(Mhat)>beta})<=delta. Combining the two separate probability estimates by a union bound proves the stated 2delta contract. No independence of the two failure events is needed.

The construction explicitly resolves the printed M-minus bracket's existence gap when q<=beta. The source's plus/minus square-root expressions should not be treated as globally nonnegative functions when their nominal right side becomes negative. The present argument only uses a well-defined deterministic population level in the q>beta case.

## Conditional-on-root-existence interpretation is false

Use the source algorithm's own constant c=(1+sqrt(2))^2=3+2sqrt(2), so 5<c<6. Set delta=exp(-1) in (0,1/2), hence L=1, and s=6. Let X=-1 with probability q=1/16 and X=0 otherwise; take p=2,u=q. This law satisfies E|X|^2=u and even the optimal-arm signed discarded-tail non-positivity condition, although Theorem5 itself does not require it.

E={nonzero count>c} is exactly the all-six-nonzero event, of probability q^6>0. On E, every X_j=-1 and
Mhat=sqrt(6/c)>1.
Since sqrt(c)=1+sqrt(2), the source upper threshold is
B=sqrt(us/((sqrt(c)-sqrt(2))^2 L))=sqrt(6/16)<1.
Thus Mhat>B on EVERY realization in E. In particular
P(Mhat<=B and tail(Mhat)<=beta | E)=0<1-2/e.
The right side is positive because e>2. This refutes the conditional reading for valid parameters of Theorem5. It does not refute the intersection-event contract: the failure event E has probability 16^(-6), far below2/e. This is a theorem-level estimator sample, not a claimed reachable Algorithm1 history at time delta^(-1/3).

## Exact source delta and scope

Accepted target proposed: the above intersection-event implication with source Eq16 constants and the exact unique-root event. The source wording 'if Mhat exists' is adjudicated explicitly rather than silently strengthened into an unconditional root-existence assumption or a conditional probability guarantee. If root existence is known almost surely, the intersection theorem reduces to the usual unconditional simultaneous bound. If only P(E)>0 is known, conditioning yields at best failure<=min(1,2delta/P(E)) from this theorem alone.

The proof derives its bounded independent concentration directly and does not rely on unread Maurer/Wang theorems. It applies at FIXED sample count s. Adaptive counts require a further valid prefix union or another stopping argument; concentration for the independently split mean and its exact constants, Eq57 count powers, forced-exploration corrections, and a full repaired regret theorem remain open. No Lean implementation or topic completion is claimed. This note is separate from the pinned source and needs independent source and mathematical reviews.

## Publication and formalization boundary

Evidence: `runs/extended-topics-20260919/genalti-concentration-audit.json` binds the unchanged private derivations and separate reviews. This page changes only source/provenance documentation. No new Lean declaration, public-root import, canary, graph node, site build, main merge or deployment is claimed. All-ten topic completion remains0/10. Functor classification: none-found-with-reason; this mathematical mechanism is not a certified cross-topic bridge.

Formalization retrieval: searched the shared HeavyTail algorithm modules and Mathlib Probability/Moments for Bernstein, sub-gamma and Chernoff interfaces, and checked the local probability theorem cards. The sub-Gaussian card (`MLIB-PROBABILITY-SUBGAUSSIAN`) provides a different quadratic MGF contract and is not evidence for the rational-denominator bound used here. No exact compiled implementation of this new root/uncentered-MGF chain was identified in that bounded search. Candidate foundations are finite independent products, exponential integrals, and measurable parameter integration in the existing project; compatibility is not yet established. Status: mathematical proof complete in the reviewed scope, Lean interface/proof work outstanding. No imported concentration theorem is hidden as an assumed consumer premise.

The subsequent `GENALTI24-ADAPTIVE-PREFIX-CONCENTRATION.md` supplies the fixed-prefix union and pathwise adaptive-count transfer for these events under explicit causal iid paired streams. That limited transfer does not establish the empirical-variance index or full regret.
