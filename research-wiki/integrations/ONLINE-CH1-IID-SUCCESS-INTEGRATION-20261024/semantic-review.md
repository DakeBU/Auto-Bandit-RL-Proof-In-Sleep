# Batch25 source/signature/blind semantic review, stage 2

Reviewer: `/root/batch25_source_reviewer`. Verdict: **accepted-with-explicit-delta** for S001–S004 as the four declared algebraic/stochastic applications. No source-to-signature or signature-to-blind-reconstruction mismatch requiring a statement repair was found. None of these four should be presented as a verbatim named theorem on printed pp1–6.

This stage was begun only after `stage1-source-topology.md` and `stage1-seal.json` were sealed. Their SHA256 values remained respectively `e76a2aae0d823ab1820c78d9cf276f21b1f9417ab080af5f04cdbb7f4163caec` and `a5054386f4c794306cf651805549076d93f63690a5d51df9eeddfda0ab0ce62f`.

The neutral packet SHA256 is `8cb9101fddd4626e3f1652cf06f48a0f4d362a89052e92668f6130d5279e393e`. Mechanical comparison confirmed each Q1–Q4 is the corresponding S001–S004 exact header after theorem-name substitution and line-ending normalization, and all four literal definitions are identical. Both blind-decoding files were read fully. No original proof body, implementation dependency file, prior review, PR prose or sourcecard was read before this verdict.

## Seven semantic slots for each anchor

| Slot | S001 / Q1 |
|---|---|
| Objects and spaces | Arbitrary real sequence `total : N -> R` and real scalar c. This abstracts the expected square-loss total and variance in Eq. (1.1)/(1.2). |
| Quantifiers | Every fixed sequence and c, then natural T tends to infinity. The conclusion is an iff, not an assertion that either condition holds for all inputs. |
| Assumptions | No logical premises. No nonnegativity, IID or policy assumption is required for this algebraic extension. |
| Conclusion and metric | Signed centered total is little-o of T iff total/T-c tends to zero. The blind decoder correctly preserves the two-sided magnitude semantics of little-o. |
| Constants and normalization | For T>0, (total(T)-Tc)/T=total(T)/T-c. At T=0 these normalized expressions need not agree; a finite exceptional term does not affect `atTop`. |
| Probability and feedback | None in the actual general theorem. Probability enters only when specializing total and c to the source setting. |
| Boundary | This is a generalized algebraic formulation of p1 success equivalence. It is not the p2 one-sided no-regret definition and does not claim arbitrary input success. |

| Slot | S002 / Q2 |
|---|---|
| Objects and spaces | A probability space, measurable IID real observations with [0,1] support a.s., a measurable seed of arbitrary measurable carrier, and measurable policies on seed times the finite strict-past real history. |
| Quantifiers | The whole data process, seed and policy family are fixed before horizon limits. `hpb` quantifies every time, every seed value and every legal bounded history. All-T nonnegativity includes T=0. The two other clauses are equivalences, not convergence assertions for all policies. |
| Assumptions | Common law and mutual independence are distinct hypotheses. Seed independence is from the entire random process, not merely pairwise independence from each observation. Policy measurability and every-legal-history feasibility are explicit sufficient model assumptions. No excess-risk identity, integrability result, nonnegative-regret fact or success conclusion is supplied as a premise. |
| Conclusion and metric | Three clauses: expected-fixed regret is nonnegative; its little-o property iff expected average square loss minus variance tends to zero; that same limit iff the Cesaro average of expected squared error from the population mean tends to zero. The last is not pointwise-in-time L2 convergence. |
| Constants and normalization | Zero-based range T is exactly T observations. T=0 regret and Cesaro MSE are zero, while centered average loss is minus variance. This finite difference does not alter either limit. The first prediction depends on seed and empty history and is not required to be 1/2. |
| Probability and feedback | Each prediction uses only S and observations with index <t. The expectation integrates both data and policy randomness on the common outcome space. The last inner integral gives a deterministic population mean, not a random outcome-dependent comparator. No high-probability, almost-sure, stopping-time or pathwise limit is asserted. |
| Boundary | Source pp1–2 motivate IID nonnegative excess and normalized success. The explicit random-seed model and Cesaro MSE criterion are derived extensions. The all-seed/all-legal-history requirement is stronger than a condition only on realized histories and must remain disclosed. The result does not claim to cover every imaginable randomized/adapted policy model or prove all policies succeed. |

| Slot | S003 / Q3 |
|---|---|
| Objects and spaces | Common-probability-space, measurable same-law observations supported a.s. on [0,1], and the concrete `meanPredict`. Temporal dependence is allowed. |
| Quantifiers | Every such process and every positive natural horizon. The process does not change with T. The comparator is one deterministic scalar for the full horizon and all outcomes, optimized after expectation. |
| Assumptions | Measurability, probability measure, common marginal law, support and positive T. No `hind`, seed or generic-policy premise. The same-law restriction is a declared stochastic specialization supporting the variance interpretation, although the pathwise upper-bound mechanism itself is broader. |
| Conclusion and metric | Expected cumulative loss minus infimum of expected fixed-scalar cumulative losses is <=4+4 log T. This is a one-sided upper bound. It is not E[pathwise hindsight regret]. |
| Constants and normalization | Exactly additive constant 4 and natural-log coefficient 4, with source t=1 corresponding to Lean t=0 and initial prediction 1/2. At later times the denominator is the number of strict-past observations. T=0 is excluded by hT. |
| Probability and feedback | Theorem 1.3 is pathwise and applies on a finite conull support intersection, then its fixed-comparator inequality may be integrated. Independence is unnecessary for this operation. |
| Boundary | This is a derived expected-fixed application of Theorem 1.3, not the printed pathwise theorem itself. It supplies no lower bound, absolute regret bound, or zero limit for dependent observations. The constant Bernoulli stream provides a direct check of that distinction. |

| Slot | S004 / Q4 |
|---|---|
| Objects and spaces | The same concrete `meanPredict`, now with a measurable IID [0,1]-valued process on a probability space. |
| Quantifiers | For each whole process satisfying the hypotheses, both natural-horizon asymptotic conclusions hold. There is no top-level T or hT binder and no generic-policy quantifier. |
| Assumptions | Common law, mutual independence, support, measurability and probability normalization. The causal information restriction is provided by the literal meanPredict formula. No asymptotic estimate or finite regret bound is an input binder. |
| Conclusion and metric | Actual convergence of expected-fixed regret/T to zero AND actual signed little-o regret. The decoder correctly distinguishes this asserted conjunction from S002's iffs. |
| Constants and normalization | No rate appears in this signature. Zero horizon is a harmless initial value of the sequence, with R0/0=0. Finite source bound and log(T)/T convergence are proof obligations, not assumptions. |
| Probability and feedback | Deterministic limits of expected quantities under the stated probability law. IID plus strict-past prediction supports the nonnegative-excess lower bound. |
| Boundary | A source-supported stochastic success corollary, not a printed corollary on pp1–6. No dependent-stream success, almost-sure realized regret, high-probability limit, minimax lower bound or arbitrary-policy success is claimed. |

## Full binder classification

Classification follows SOURCE / STANDING / TYPING / RULED / EXCESS. SOURCE means an explicit premise of either the cited source setting or the explicitly identified derived-application contract. For added randomized-model assumptions the `basis` column expressly says **derived D2**, so this classification cannot be reused to label those assumptions as literally printed. There is no human-approved source correction and no RULED binder. Under the declared application contracts, no EXCESS proof-ingredient binder was found. If S002 were instead advertised as an exact transcription of a printed theorem, its added model assumptions and MSE conclusion would require rejecting that stronger attribution.

| Anchor(s) | Binder(s) | Class | Basis and expanded meaning |
|---|---|---|---|
| S001 | total | TYPING | Arbitrary real-valued natural sequence, replacing the special loss total in the declared algebraic extension. |
| S001 | c | TYPING | Arbitrary fixed real centering constant. |
| S002–S004 | Ω, universe u | TYPING | Outcome carrier and universe level, not random variables or extra mathematical restrictions. |
| S002–S004 | MeasurableSpace Ω | TYPING | Event structure needed for the stated probabilities and integrals. |
| S002–S004 | μ | TYPING | The common measure on Ω. |
| S002–S004 | IsProbabilityMeasure μ | STANDING | The source uses probability distributions and expectations. Expansion: μ has total mass 1. |
| S002–S004 | Y | TYPING | Whole real observation process indexed by natural time. |
| S002–S004 | hY | TYPING | Every Yt is measurable, making the source's random variables/expectations well-typed. No boundedness or independence is hidden in this binder. |
| S002–S004 | hlaw | SOURCE | For every t, Yt and Y0 have identical law under μ. Explicit fixed common distribution on p1, retained in D2–D4. IdentDistrib also includes the usual almost-everywhere measurability component; hY is stronger explicit measurability, not a proof result. |
| S002–S004 | hb | SOURCE | For every t, Yt belongs to [0,1] μ-a.e. This is the probabilistic representation of source bounded observations. Literal order is ∀t then a.e.ω. Countability permits a common conull event, but no such event is supplied as a hypothesis. |
| S002, S004 | hind | SOURCE | IID premise expanded as mutual independence of the entire family in the finite-subfamily sense. It is not merely pairwise independence. |
| S002 | Seed, universe v | TYPING | Arbitrary seed carrier for the explicitly declared D2 randomized-model extension. |
| S002 | MeasurableSpace Seed | TYPING | Event structure of that seed carrier. No topological/standard-Borel hypothesis is imposed. |
| S002 | S | TYPING | Seed random variable on the same outcome space, not a new probability space or fresh-per-round seed sequence. |
| S002 | hS | TYPING | Seed measurability in derived D2. |
| S002 | hseed | SOURCE | **Derived D2 model premise:** S is independent of the entire function-valued process ω↦(t↦Ytω). It is not literally printed on pp1–6. This is an explicit sufficient model for internal randomization and is not the desired current-risk decomposition. |
| S002 | policy | TYPING | **Derived D2 interface:** for each t, a real output function on Seed × (range t → R). The finite index subtype enforces strict past by construction. |
| S002 | hp | TYPING | Every policy_t is measurable on that product/function measurable space. |
| S002 | hpb | SOURCE | **Derived D2 admissibility premise:** ∀t,s,z, if every history coordinate belongs to [0,1], then policy_t(s,z) belongs to [0,1]. This models legal outputs on all legal histories and seed values, including unrealized inputs. No integrability or risk estimate is assumed. |
| S003 | T | TYPING | Natural finite horizon. |
| S003 | hT | STANDING | Positive horizon, implicit in source Theorem 1.3 and its log/division formulas. |

All nested binders are also accounted for. The internal t in hY/hlaw/hb/hp is a universal natural index (TYPING); ω in hb is bound by the a.e. quantifier (TYPING under the SOURCE support premise). In hpb, t,s,z and i are time, seed value, real history and its finite index (TYPING), while the coordinatewise boundedness antecedent is SOURCE as part of the legal-history domain. The ω,t in hseed's lambda are outcome and natural process coordinate (TYPING). The locally defined `prediction` is a conclusion-side let binding, not an assumed predictor; its t,ω,i binders are TYPING. The T in S002's first conjunct is a universal conclusion, and all other T lambdas are sequence arguments. Sum variables range over 0,...,T-1; every integral ω is local, including the separately bound inner integral defining the population mean. These are TYPING binders and introduce no logical premises. Little-o accuracy parameters/eventual thresholds and Tendsto neighborhood quantification are the standard meanings of the conclusion, not hidden hypotheses. S004's conjunction introduces no witness.

The four literal definitions have no project-owned Prop bundles or theorem-premise fields to recursively expand. `empiricalMean` takes sequence y and natural n, with bound sum index t; `meanPredict` takes sequence y and time t and uses an equality test, not a hypothesis. `expectedFixedMinimum` and `expectedFixedRegret` have Ω, its measurable structure, μ, process data and T, with local u,ω,t as appropriate. These are all TYPING. Their absence of probability/integrability assumptions does not license ordinary finite-expectation claims outside the reviewed theorem hypotheses.

## Literal-definition and benchmark audit

- `empiricalMean` is literal finite sum divided by n; n=0 is 0 by Lean's total real division. The source's positive-prefix minimizer is not characterized at n=0.
- `meanPredict` explicitly gives 1/2 at time 0 and the exact prior empirical mean at t>0. This is the source-prescribed initialization, not a fallback for a failed minimizer choice. It agrees with Theorem 1.3 after the index shift.
- `expectedFixedMinimum` literally takes real sInf of the image of [0,1] under u↦E sum(u-Yt)^2. The optimization is after expectation. Under bounded common-law hypotheses the required identity is E sum(u-Yt)^2=T(v+(u-m)^2), with m in [0,1]. This establishes nonempty bounded-below image and attainment at m, so sInf equals the printed minimum. At T=0 the image is {0}. This calculation remains an implementation proof obligation, not something certified by a name or type alone.
- `expectedFixedRegret` literally subtracts that benchmark from the learner's expected total. It neither moves the minimum inside expectation nor lets the comparator depend on the seed, history or outcome. The benchmark definition chooses an optimum separately for each horizon; common-law assumptions happen to permit the same m at every positive horizon.

## Independent anti-anchoring checks

1. Setting a signed centered sequence equal to -T would satisfy a one-sided upper-sublinear condition but not little-o. S001 uses the latter, so it matches the p1 zero-limit criterion and cannot be used as the p2 one-sided definition.
2. A constant or otherwise poor legal policy need not converge to the population mean. S002 gives iffs and nonnegativity, so it does not incorrectly assert such convergence.
3. Same-law perfectly dependent Bernoulli observations give expected excess (1-T)/4 for the historical mean learner at T>=1. S003 is compatible with this and S004 excludes it through mutual independence.
4. The final S002 integral's inner ω is a fresh binder. Its comparator is the deterministic population mean, and the conclusion averages expected squared errors. It does not measure errors from a trajectory's empirical mean or imply per-time L2 convergence.
5. Theorem 1.3's output is deterministic pathwise, whereas S003/S004 use expected-fixed regret. The proposed lifting uses a one-sided comparator comparison, not a false equality between E[min] and min E.

## Result and remaining scope

All four blind reconstructions match the exact sealed signatures in all seven slots. The source supports the advertised mathematical mechanisms when the explicit algebraic, randomized-model, dependent-stream and stochastic-corollary deltas remain visible. The semantic verdict is therefore accepted-with-explicit-delta, not exact printed-theorem identity. No source repair is proposed.

No proof body, compiled dependency, axiom set, actual implementation consumer, build or publication surface was assessed in stages 1–2. Each identity, independence composition, integrability fact, minimum attainment, deterministic regret import and asymptotic limit must still be supplied internally and checked independently. This report provides no closure, merge or reference-retirement authorization.


---
Public location projection of private evidence batch25-source-review-v1/stage2-semantic-review.md. Original SHA256: `7286525759b10df1dc604c4cfc406d29d4701023f74dbbdde9ae72d308db3a87`. Physical paths alone are logicalized; original stage wording and limits remain unchanged. Later bounded status is recorded in review-binding.json.
