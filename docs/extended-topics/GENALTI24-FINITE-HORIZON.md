# Genalti Theorem 2: finite-horizon quantifier adjudication

Source: COLT2024/PMLR247 genalti24a.pdf, SHA256 65eceb2cd402baa8c7f5b60d273a103fbd181cf6803a4b7f0d2f4092742fe5b6. Eq5/Eq6 on printed p7; proof pp17-19. Mathematics independently accepted by repair and source reviewers; Lean prototype compiled separately.

Fix p=1+epsilon in (1,2], K>=2, finite natural T, u>0. Each stationary arm law nu_i is a probability measure with integral |x|^p<=u. A randomized adaptive policy can be represented on its actual probability space by measurable actions I_t in {1,...,K}; no confidence or algorithm hypothesis is needed. This is the expected pseudo-regret contract of source Eq1.

The first moment exists because |x|<=1+|x|^p. Jensen on the nonnegative integrable variable |X| gives (E|X|)^p<=E|X|^p<=u, hence |mu_i|<=E|X|<=u^(1/p). Therefore every gap mu_max-mu_i is in [0,2u^(1/p)]. Pathwise the sum of T selected gaps is in [0,2T u^(1/p)], so it is integrable for every measurable action process and its expectation R_T has the same bounds. Dividing by the positive scale gives 0<=R_T/u^(1/p)<=2T. The result includes T=0. It is valid for every algorithm separately and for all u>0 and all admissible arm laws; taking the joint supremum for any fixed algorithm and T preserves the finite bound2T. If using extended-real suprema, the same upper bound applies. The displayed Eq5 equals infinity is consequently false at every finite T, including every proposed sufficiently large fixed T.

At u=0, all rewards vanish almost surely and regret is zero. The ratio0/0 has no ordinary real meaning; excluding this boundary suffices to refute the infinity claim on its meaningful positive-scale domain. A convention assigning zero at u=0 cannot change the upper bound.

Sharpness as a universal bound over algorithms: for any u>0, let s=u^(1/p), choose two deterministic laws delta_s and delta_(-s), and always select the second arm. Both raw p-moments equalu and regret=2Ts, so the normalized value is2T. This does NOT assert sharpness for every fixed algorithm, nor a minimax lower bound.

## Necessary horizon dependence of Eq6

Let rho=u'/u>=1, u>0, and suppose the stated Eq6 lower bound is valid for its two instances:
 max(R_T(nu)/u^(1/p), R_T(nu')/(u')^(1/p)) >= c1 rho^((p-1)/p^2) T^(1/p), c1>0.
For T>0 each normalized term is <=2T. Thus
 T^((p-1)/p) >= (c1/2) rho^((p-1)/p^2),
and hence
 T >= (c1/2)^(p/(p-1)) rho^(1/p).
The required horizon cannot be chosen uniformly over arbitrary rho. This is a necessary condition, not a proof of sufficiency or of Eq6. The proof's p19 chosen gap has the form constant(p,c)*T^(-(p-1)/p)*u^(-(p-1)/p^2)*(u')^((2p-1)/p^2). Dividing by its allowed upper scale (u')^(1/p) leaves constant*T^(-(p-1)/p)*rho^((p-1)/p^2), confirming the same ratio-dependent admissibility issue. No numerical constant is inferred from unreadable text.

The repair of quantifier order that could express the intended asymptotic impossibility is a separate theorem. For example, if Eq6 were independently established for every fixed rho at sufficiently large horizons depending on rho, it could refute a single u-uniform rate constant by choosing rho first, then an admissible T. It cannot imply an infinite scale-normalized regret supremum at a fixed T. This note does not certify Eq6, the original lower-bound dependency proofs, or a repaired adaptive algorithm/regret theorem.

## Formalization route

Reuse the existing realMeanRegret/realMeanGap definitions and integrable_id_of_raw_moment. Use Mathlib convexOn_rpow and ConvexOn.map_integral_le to derive the mean bound, then finite gap summation and probability integration. Keep the policy arbitrary and measurable rather than substituting a specific UCB policy. The fixed-T cap is a strict source obstruction; it is not a new learning-rate result. No whole-topic completion follows.


## Additional source-review boundary

The source reviewer also checked the base-instance constraint Delta<u^(1/p)
on p17. For the selected gap this imposes a stronger ratio-dependent condition
than the alternative-scale check on p19. The restricted minimization interval
[0,T], distribution admissibility and KL conditions remain necessary before
any corrected lower-bound theorem can be accepted. Neither the necessary
horizon inequality above nor the finite cap supplies those missing steps.

## Lean prototype and integration state

`runs/extended-topics-20260919/GenaltiFiniteHorizon.lean` contains the current
prototype. It derives the mean bound using Jensen, the deterministic gap sum,
and the normalized expected regret cap on an arbitrary probability space with
measurable actions. Local `lake env lean` compilation succeeded; the endpoint
uses only propext, Classical.choice and Quot.sound. The prototype actually
allows epsilon>=0 and K>=1, which generalizes the source range. The supplied
integrability of the raw moment is explicit. The regret random variable's
integrability is derived, not assumed.

It is not imported by the public root. It has no production semantic acceptance,
nondegenerate public canary, contribution manifest, graph mapping or new shared
gate. No formal supremum theorem, sharpness witness or necessary-horizon-power
inequality is claimed to be implemented in this prototype. The mathematical
adjudication and its future formal integration remain separate.

The source/provenance ledger changes; Lean/Overview/Functor graph, teaching,
website results and contributor surfaces have no change because this is not
a public production declaration. Functor classification: none-found-with-reason;
this elementary moment-cap argument adds no certified cross-setting bridge.
All-ten topic completion remains0/10; no main merge, deployment, or new ICLR
controlled experiment is asserted.

Blind reconstruction confirms the arbitrary measurable-action upper-cap contract,
with no assumed regret bound, changed action or changed probability measure.
The packet redacts only the namespace; exact correspondence is recorded in
`runs/extended-topics-20260919/genalti-fixed-horizon-audit.json`.

Independent anti-anchored source review also accepts the prototype as this
generic per-instance cap with explicit generalizations, after reading the
blind reconstruction. It does not accept a formal source-class/supremum
obstruction or production integration.
