# Derived application obligations, separate from printed topology

Status: mathematical source/application analysis proposed by the extractor. Independent review is pending. These statements are not printed theorems in this source region and have no Lean-verification status in this packet.

## Notation and boundaries

For integer T>=1, let L_T=sum_{t=1}^T(X_t-Y_t)^2. For a probability law nu supported on [0,1], write mu=E_nu[Y] and v=E_nu[(Y-mu)^2]. Define C_T=E[L_T]-Tv and A_T=E[L_T]/T-v. Expected-fixed regret is F_T=E[L_T]-min_{u in [0,1]}E[sum_{t=1}^T(u-Y_t)^2]. Pathwise hindsight regret is H_T=L_T-min_{u in [0,1]}sum_{t=1}^T(u-Y_t)^2. These are different benchmarks. In particular F_T is not generally E[H_T].

The time sequence should be one coherent learner/observation process for the limiting statements, or else a deliberately specified horizon-indexed family. Source page 1 does not explicitly quantify this distinction. T=0 is outside the printed logarithmic theorem; arbitrary definitions at zero do not change limits at infinity, but must not be used to claim a literal zero-horizon source theorem.

## D1: normalization equivalence for signed centered totals

Let b_T be any real total and c any real constant. Set C_T=b_T-Tc and A_T=b_T/T-c. For T>=1, A_T=C_T/T exactly. Consequently C_T=o(T) iff A_T tends to zero. The usual signed little-o definition is |C_T|/T ->0; equivalently C_T/T ->0. No nonnegativity, IID assumption or policy model is needed for this algebraic equivalence.

Source support: P01-EQ11, P01-EQ12, P01-SUCCESS. Missing formal bridge: GAP-NORMALIZATION. D1 extends the algebra to arbitrary signed totals. It must not identify the page 2 one-sided no-regret condition with two-sided little-o. An upper bound C_T/T<=epsilon eventually does not alone give C_T/T->0.

Required internal obligations: positive-horizon division identity, signed little-o/quotient equivalence, and handling of finitely many initial indices. These belong in dependencies, not public convenience hypotheses.

## D2: explicit randomized causal-history policy success equivalence

A concrete admissible model is a probability space carrying IID [0,1]-valued observations (Y_t) and a seed U independent of the entire observation stream. Each X_t is a measurable [0,1]-valued function of U and (Y_1,...,Y_{t-1}); equivalent policy kernels or a sequence of private random coins are possible if their conditional independence from future observations is made explicit. At t=1 only internal randomness is available. The expectation is over both data and policy randomness. Measurability of the policy and boundedness ensure the finite losses, products and sums are integrable.

Under this model, X_t is independent of Y_t, and the centered cross term vanishes. Thus E[(X_t-Y_t)^2]=v+E[(X_t-mu)^2]. Summing gives C_T=sum_t E[(X_t-mu)^2]>=0. Independently, for each fixed u, E[sum_t(u-Y_t)^2]=T[v+(u-mu)^2], with mu in [0,1], so F_T=C_T. Hence the following criteria are equivalent: C_T=o(T); A_T->0; F_T=o(T); F_T/T->0. This asserts equivalence of success criteria for any admissible policy, not universal success of all policies.

Printed evidence: information order P01-GAME, IID setting P01-IID, mean benchmark P01-ORACLE, displays and success P01-EQ11/P01-EQ12/P01-SUCCESS, fixed expected benchmark P02-FIXED. The source does not print the seed model, a randomized policy theorem, a conditional expectation proof, or these four criteria as a named theorem. The explicit randomized model is an application/generalization requiring separate source/semantic review.

Application SOURCE_GAP obligations:

- APP-POLICY-MODEL: specify measurable history carrier, finite-history projection and independent internal randomness; no current/future observation enters X_t.
- APP-POLICY-INDEP: derive current-observation independence from IID data and the seed/history model; do not assume the desired cross-term or squared-loss decomposition as a public premise.
- APP-INTEGRABILITY: discharge measurability and integrability for all finite expected quantities.
- APP-RISK-IDENTITY: derive the vanishing cross term and nonnegative excess.
- APP-FIXED-IDENTITY: prove the expected fixed minimum identity; minimization stays outside expectation.
- APP-CRITERIA: combine identities and D1.

For the bare normalization equivalence, these causal/IID assumptions are mathematically unnecessary. They matter to the source's interpretation as nonnegative excess above the best admissible prediction and to later convergence by squeezing.

## D3: expected-fixed 4+4 log T upper bound for the deterministic mean learner

Let each Y_t have the same law nu on [0,1], on a common probability space; dependence between different observations is allowed. Let X_1=1/2 and X_t=(1/(t-1))sum_{i<t}Y_i for t>=2. Theorem 1.3 is deterministic and pointwise, so it applies to each bounded realized observation path. If boundedness is only almost sure, use the finite intersection of the T support events for each horizon before integrating.

For any fixed u in [0,1], pointwise min_z sum_t(z-Y_t)^2<=sum_t(u-Y_t)^2. Consequently L_T-sum_t(u-Y_t)^2<=H_T<=4+4 ln T. Choose u=mu, integrate the inequality, and use E[sum_t(mu-Y_t)^2]=Tv. Since same-law marginal moments also give min_u E[sum_t(u-Y_t)^2]=Tv, one obtains F_T=C_T<=4+4 ln T. Independence is not needed for this upper bound.

Source inputs: P04-THM13 with its entire proof chain, P02-FIXED and the mean benchmark P01-ORACLE. The stochastic lifting and dependent-stream claim are derived applications, not printed statements of Theorem 1.3.

Application SOURCE_GAP obligations:

- APP-MEAN-CAUSAL: construct the deterministic strict-past mean sequence, measurable and in [0,1], retaining the exact 1/2 initialization.
- APP-PATHWISE: instantiate Theorem 1.3 on each bounded path, discharging support and horizon conditions.
- APP-COMPARATOR: pathwise comparison to mu before taking expectation, with inequality direction as above.
- APP-INTEGRABILITY: bounded finite sums and losses support monotonicity and linearity of expectation.
- APP-FIXED-IDENTITY: expected fixed minimum equals Tv for common marginal law.

An alternative sufficient route uses E[H_T]<=B_T and E[min_u loss(u)]<=min_u E[loss(u)], so F_T<=E[H_T]<=B_T. This is an OR alternative, not an additional AND dependency of the fixed-mu route. It requires measurability/integrability of the empirical-minimum random variable. No interchange E[min]=min E is allowed.

The same-law dependent setting does not imply F_T>=0. For example, if Y_t=Z for all t with one Bernoulli(1/2) random variable, then the learner's total loss is 1/4, while Tv=T/4, so C_T=(1-T)/4. Thus the upper bound alone does not imply normalized convergence to zero or little-o. This elementary diagnostic example is extractor-derived, not a printed source example.

## D4: IID mean learner normalized expected excess tends to zero and is little-o

Restore IID observations and use the same deterministic strict-past mean learner with X_1=1/2. D2's causal-risk identity applies with a constant seed, giving C_T>=0. D3 gives C_T<=4+4 ln T. Dividing by T>0 yields 0<=A_T<=4/T+4 ln(T)/T. The right side tends to zero, so A_T->0 and D1 gives C_T=o(T). The same statements hold for F_T=C_T.

This is a source-supported derived application, not a printed stochastic corollary on pages 1–6. It requires the analytic limit ln(T)/T->0 and the causal/IID nonnegative lower bound in addition to Theorem 1.3. It proves expected performance, not almost-sure, high-probability or uniform-over-laws convergence unless those stronger quantifiers are separately established.

Application SOURCE_GAP obligations:

- APP-IID-LOWER: D2 risk identity specialized to the deterministic strictly-past learner.
- APP-LOG-SUBLINEAR: prove the logarithmic envelope divided by T tends to zero, including positive natural-to-real horizon conventions.
- APP-SQUEEZE: combine the lower and upper bounds to obtain the zero limit.
- APP-LITTLEO: apply D1, preserving signed little-o rather than one-sided no-regret.

D4's selected route is AND(D2 lower, D3 upper, logarithmic limit, normalization). An independently derived exact IID risk calculation could supply a different OR-route, but no such route is printed in this region or supplied as a proved node here.

## Public-assumption audit guidance

Literal source premises: [0,1] observations/predictions, fixed common law and IID in the stochastic discussion, arbitrary deterministic path in Theorem 1.3, strictly-past empirical mean, initial 1/2, positive finite horizon. A measurable probability space is implicit typing/regularity for expectations. An explicit seed model is an added formalization/generalization of admissible randomized policies, not a printed binder. The risk decomposition, nonnegativity, fixed-benchmark identity, pathwise regret bound, envelope limit and convergence must be proved or reused internally; making them public hypotheses would convert the intended conclusions into conditional wrappers.

The inventory and obligations above were written before sealed public headers were supplied. A subsequent public-interface-only mapping follows. Distinct review remains required before declaring source fidelity.

## Sealed public-interface mapping (post-extraction)

Only `actual-headers.json` and `literal-context.json` in `batch25-statement-seal-v1` were read. No proof bodies or additional seal/rationale files were read. The interface uses zero-based rounds: Lean round t corresponds to source round t+1, `range T` has exactly T losses, and `meanPredict` at t>0 averages exactly indices 0,...,t-1. Its t=0 prediction is 1/2. This is the source's strictly-past learner, including its initialized first round.

| Header | Source/application mapping | Additional obligation visible from the interface |
|---|---|---|
| S001 `centered_total_sublinear_iff_average` | D1; signed algebraic characterization corresponding to the source equivalence | Arbitrary real totals and constants are an algebraic generalization. The value at T=0 does not affect `atTop`. |
| S002 `randomized_history_policy_success_iff` | D2; source-inspired explicit randomized causal-history formulation | In addition to nonnegativity and success equivalence, the final conjunct equates convergence of A_T with convergence of M_T=(1/T)sum_{t<T} E[(X_t-mu)^2]. Derive C_T=sum_{t<T}E[(X_t-mu)^2] internally, then divide for T>0. At T=0, only the all-horizon nonnegativity conjunct requires direct empty-sum/zero-minimum handling. |
| S003 `meanPredict_expectedFixed_upper` | D3; expected-fixed application of Theorem 1.3 for positive T | `hlaw` and support allow dependent streams. No independent-current-observation premise appears, consistently with an upper bound alone. |
| S004 `meanPredict_iid_success` | D4; derived IID success corollary | Joint conclusion is convergence of expected-fixed regret divided by T and signed little-o; requires the IID causal lower bound plus logarithmic upper bound. |

S002's measurable seed S is independent of the full stream, and the policy takes only S and the subtype of indices in `range t`. Its output bound is required on every bounded history and seed. This supplies an explicit all-history admissible policy model; the printed source does not specify this universal policy interface. The source-inspired extension must remain labeled as such.

`expectedFixedMinimum` is represented by `sInf` of the image of the expected-loss function over [0,1], whereas the source writes a minimum. APP-FIXED-IDENTITY must therefore establish nonempty bounded-below image and attainment at the mean (or equivalent complete characterization) before identifying the `sInf` with Tv. For T=0 the image is the singleton {0}. The four literal definitions expose no added theorem-like assumption. The extractor has not verified their referenced implementation bodies or proof dependencies.

The final S002 mean-squared-prediction criterion is not separately printed in pages 1–6. It is a direct derived identity from the missing causal risk expansion, and is recorded as `APP-MSE-CRITERION`, not a new printed theorem node.


---
Public location projection of private evidence batch25-source-extraction/derived-obligations.md. Original SHA256: `19b9e72c9b1ffe7c97e341ce9f25bfbc2a7eb73bee5de7920349b5ddd0bf7f2c`. Physical paths alone are logicalized; original stage wording and limits remain unchanged. Later bounded status is recorded in review-binding.json.
