# Park2026 Theorem3: literal obstructions and a qualified causal IPW repair

Date: 2026-09-20. Proposed source adjudication and independent mathematical repair.
Source: Park, Cho and Lee, Boltzmann Exploration for Heavy-Tailed Bandits, PMLR300/AISTATS2026, park26a.pdf SHA256 c192f3345a20227243a822e8fc60d2fd0b8f71d44d5f5f3cc7e35f267d33d102. Theorem3 Eq4 PDFp5, AppendixC pp16–20, especially Eq78–82 and Eq100–109. This note does not repair the H-BE regret theorem.

## 1. Literal finite-M zero denominator

Take K=2, a uniform logging policy at every round, both reward laws deterministic1, and any p in(1,2] with raw moment bound nu=1. The uniform target value is1. Every selected true propensity equals1/2, satisfying even the stronger actionwise support floor d=1/2.

For each selected action, generate M>=1 independent policy-replay Bernoulli indicators of success probability1/2, as in the source propensity approximation. Their average phat is zero with probability2^(-M)>0. Thus at any finite M, the printed estimator containing reward/(2phat) is not a real-valued random variable on a positive-probability event. If positive reward divided by zero is interpreted as positive infinity, its unconditional expected absolute error is infinite, even at a fixed T>=1 (one zero denominator suffices). This persists for every finite M0 and M>=M0. No finite unconditional expected-risk inequality follows from merely making the zero event rare.

With exact true propensity the same example has IPW estimate exactly1 and zero error. This distinguishes a propensity approximation defect from a heavy-tail phenomenon. Defining reciprocal zero to be zero in a totalized algebra or numerical implementation would be a different estimator with a separate bias analysis, not the printed mathematical division.

The source wording 'with probability1-delta, expected loss ...' does not identify which randomness is averaged and which is conditioned. The example rules out the ordinary UNconditional finite-risk reading of the unregularized MC estimator; it does not rule out a carefully stated good-event conditional claim or a regularized estimator.

## 2. Selected-action support alone is insufficient

Take K=2, arm1 deterministic0, arm2 deterministic1, and a logger that always selects arm1. The uniform target value is1/2; raw p moments are at most1. The true selected propensity is always1, hence satisfies the printed selected-action floor for d=1/2. Its MC estimate is identically1 for every M. The printed IPW estimate is always0 and its absolute error is1/2 for every T and M.

The claimed right-hand side with fixed p-only finite constants tends to0 as T,M increase. Consequently the selected-action-only premise cannot establish that theorem for a uniform target. There is no Monte Carlo zero problem or residual probability ambiguity in this deterministic counterexample. What is missing is support of ALL target actions at each history. Exact H-BE softmax has positive actionwise probabilities after initialization, but the general Theorem3 premise does not state that property or a common actionwise floor. Initialization requires separate treatment if its deterministic rounds are included in a target-overlap assertion.

Source target qualification: Appendix C Eq66 instead defines mu as T^(-1) sum_t E[R_t/(K pi_t,I_t)]. In this deterministic-logger example that quantity is zero, so this example does NOT refute a numerical bound for the appendix-defined target. It refutes identification of that target with the stationary uniform-policy value under selected-only support. The distinction is a main-text/appendix target contract gap, and full actionwise overlap restores the equality in the repair below.

## 3. Source drift calculation cannot supply decay

Eq108 gives, with notation A_T from the source,
 (E|A_T|^p)^(1/p)<=2 T^(1-1/p) (sum_t E|Xhat_t|^p)^(1/p).
Substituting its Eq100 bound E|Xhat_t|^p<=nu/(Kd)^p and dividing by T gives exactly2nu^(1/p)/(Kd), not that quantity times T^(-(1-1/p)). The powers are T^(-1)*T^(1-1/p)*T^(1/p)=1. This identifies the invalid implication to Eq109, without pretending that true-propensity IPW cannot have a decaying risk. Conditional unbiasedness provides the correct alternative below.

## 4. Explicit repaired probability model

Fix K>=1, T>=1, p in(1,2], finite nu>=0, and d in(0,1). Let (F_t) be an increasing filtration containing all actions, rewards and replay variables through round t. At each round t a history sigma-field F_(t-1) determines a measurable categorical logging law pi_t on all K arms, with pi_t,i>=d almost surely for EVERY arm. Necessarily Kd<=1. Draw I_t according to that law and reward R_t whose conditional law given F_(t-1),I_t=i is the stationary arm law D_i. These laws satisfy integral|x|^p<=nu and have means mu_i. Let mu_bar=(1/K)sum_i mu_i, the stationary uniform-target value.

The true-propensity variable is Z_t=R_t/(K pi_t,I_t). Conditional averaging over the categorical action gives
 E[Z_t|F_(t-1)]=mu_bar,
 E[|Z_t|^p|F_(t-1)]<=nu/K^p * sum_i pi_t,i^(1-p)
                         <=nu/(Kd)^(p-1)=v.
All moments here are RAW reward moments. Full actionwise overlap is essential for the cancellation, and a centered-noise bound alone does not replace this premise.

Let M>=1. Conditional on the history and selected action, obtain M fresh independent Bernoulli(pi_t,I_t) replays; assume these are independent of the current reward conditional on that same history/action. Denote their mean phat_t and define the explicitly clipped estimator
tilde_pi_t=max(d/2,phat_t),
tilde_mu=(1/T)sum_t R_t/(K tilde_pi_t).
All denominators are positive. The clipping floor requires a known d; it is an added estimator input and an explicit change from the source. The true-propensity result below needs no MC replays or clipping. The logging policy may depend on past rewards and any past replay randomness included in F_(t-1); only the stated current conditional laws and independence are needed.

## 5. Elementary scalar martingale p-moment producer

For r=p-1 in(0,1], h(x)=sign(x)|x|^r obeys
 |h(x)-h(y)|<=2^(1-r)|x-y|^r.
On the same half-line this follows from subadditivity of z^r on nonnegative reals; on opposite half-lines, concavity gives a^r+b^r<=2^(1-r)(a+b)^r. Since the derivative of |x|^p is p h(x), integrate along the segment x+ty, 0<=t<=1, to obtain
 |x+y|^p<=|x|^p+p h(x)y+2^(2-p)|y|^p.
The factor p cancels integral_0^1 t^(p-1)dt=1/p. This includes p=2.

Let D_t=Z_t-mu_bar. Conditional centering gives E[D_t|F_(t-1)]=0, and conditional Jensen plus |a-b|^p<=2^(p-1)(|a|^p+|b|^p) gives E|D_t|^p<=2^p v. Apply the preceding scalar inequality successively to S_t=sum_(r<=t)D_r. Its cross term has expectation zero: S_(t-1) is past measurable and Holder ensures integrability of |S_(t-1)|^(p-1)|D_t|. Finite sums are in Lp, or this follows inductively; truncating the past-measurable coefficient justifies conditional integration without assuming boundedness.

Consequently
 E|S_T|^p<=2^(2-p) sum_t E|D_t|^p<=4Tv.
By Holder on the probability space, E|S_T|<=(E|S_T|^p)^(1/p). Thus the ACTUAL true-propensity IPW estimator mu_true=(1/T)sum Z_t satisfies
 E|mu_true-mu_bar|<=4^(1/p) nu^(1/p)/(Kd)^((p-1)/p) * T^(-(p-1)/p).
No assumption of independence across the adaptive Z_t is used; it is a martingale-difference proof. No predictable drift term remains because the target conditional mean is the constant mu_bar. nu=0 is immediate by zero rewards almost surely.

## 6. Clipped Monte Carlo error and unconditional finite risk

Since pi_t,I_t>=d, projection onto[d/2,infinity) cannot increase its distance from the truth:
 |tilde_pi_t-pi_t,I_t|<=|phat_t-pi_t,I_t|,
 |1/tilde_pi_t-1/pi_t,I_t|<=2|phat_t-pi_t,I_t|/d^2.
Conditionally on history and I_t, Bernoulli variance and Cauchy–Schwarz give
 E|phat_t-pi_t,I_t|<=sqrt(pi_t,I_t(1-pi_t,I_t)/M)<=1/(2sqrt M).
Conditional independence of the replay and reward, together with E[|R_t||history,I_t]<=nu^(1/p), therefore gives
 E|R_t/(K tilde_pi_t)-Z_t|<=nu^(1/p)/(K d^2 sqrt M).
Triangle inequality over the actual average then proves the complete unconditional repaired endpoint
 E|tilde_mu-mu_bar|<=4^(1/p) nu^(1/p)/(Kd)^((p-1)/p) * T^(-(p-1)/p)
                       +nu^(1/p)/(K d^2 sqrt M).
This holds for every finite M>=1 and T>=1, not merely on an unspecified high-probability event. It changes the estimator and support assumptions explicitly. Since Kd<=1, the first term is also bounded by4^(1/p)nu^(1/p)/(Kd T^((p-1)/p)), so the source-order denominator can be retained as a looser consequence.

## 7. Optional precise good-event interpretation of the raw estimator

Let G={phat_t>=d/2 for all selected t<=T}. For a conditional Bernoulli sum with mean Mpi, the bounded independent MGF proof already used in the Genalti root reconstruction gives
 P(sum-Mpi<=-Mpi/2 |history,I_t)<=exp(-Mpi/8)<=exp(-Md/8).
Since d/2<=pi/2, the event phat_t<d/2 is contained in that lower tail. A union over the T actually estimated selected propensities yields P(G^c)<=T exp(-Md/8), without any independence across rounds. Thus M>=(8/d)log(T/delta) ensures P(G)>=1-delta for delta in(0,1).

On G the raw and clipped estimators coincide. If B denotes the unconditional finite-risk right side from section6, then
 E[|mu_raw-mu_bar| | G]<=B/P(G)<=B/(1-delta).
This is a risk conditional on the explicitly defined JOINT good event, not a probability statement about an unqualified expectation and not an assertion that the raw unconditional risk is finite. The restriction of mu_raw to G is well-defined; no value outside G is needed for this conditional assertion. The sample size has explicit T dependence, unlike the printed M0(d,delta) without horizon dependence.

## 8. Boundaries and source disposition

The two finite examples adjudicate the literal zero-denominator and missing-overlap obstructions. The drift exponent error is algebraic. The positive result is a complete source-adjacent repair for stationary uniform-target evaluation under a causal logging law with actionwise overlap, using either true propensities or an explicitly floor-clipped MC estimate. All probability producers used here are derived; no von Bahr–Esseen/Marcinkiewicz–Zygmund theorem is assumed unread.

This is not a proof of H-BE regret, an author correction, a claim of novelty for IPW martingale concentration, an evaluation experiment, or a Lean theorem. H-BE initialization and the existence or T-dependence of a common actionwise d must be established separately before this theorem can be instantiated on its full trajectory. Arbitrary sequential target policies, centered-noise-only contracts, history-dependent target values and unregularized MC unconditional risk are outside the accepted target.


Review status and source/artifact hashes are recorded separately in `runs/extended-topics-20260919/park-adjudication-audit.json`. These are mathematical audit documents, not Lean declarations.
