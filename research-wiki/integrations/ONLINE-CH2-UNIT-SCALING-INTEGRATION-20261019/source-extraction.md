# Retained source extraction and separate review status

This is the normalized historical extraction record. Its original proposed-state wording below is preserved. The independent source-only review and later bounded semantic review are separately bound in source-topology.json and source-map.json. Source-page image/text labels refer to private retained evidence, not public file links. This packet does not claim unrestricted source-gap closure or final candidate acceptance.

# Batch18 source-only extraction: unit analysis and meter/kilometer example

Status: extracted and proposed, awaiting a distinct source-only topology reviewer. No Lean implementation, canary, historical unit-scaling semantic verdict, or root Lean reconstruction was consulted. The extractor does not approve this topology or any mathematical repair.

## Pinned source and verified locator

Francesco Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*, arXiv:1912.13213v10, 21 June 2026. PDF SHA256: `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, 3,483,459 bytes. Title, author, revision and date were visually checked on PDF1.

The exact subsection is **2.2.3 Unit Analysis Bits**, within Section2.2. It starts on printed20/PDF32 beneath Example2.32 and ends on printed22/PDF34 immediately before Section2.3. The requested core learning-rate, regret-unit and meter/kilometer formulas are on printed21–22/PDF33–34. Printed21's running header is the enclosing Section2.2 title, not the subsection locator. No historical PR locator was used as scientific evidence.

Primary complete page images: source-page-032.png, source-page-033.png, source-page-034.png. Additional directly inspected source context is printed13–14/PDF25–26 (full fixed-rate bound and negative residual), printed16–17/PDF28–29 (subgradient definition and nonunique selections), and printed19/PDF31 (OSD proof transfer/Lemma2.31). PDF35 is preserved to establish the neighboring historical/exercise boundary. All page pixels/text and hashes are listed in the extraction receipt.

## Attributed source claims and formulas

The author assigns prediction unit `[x]` and loss unit `[ell]`. Unit matching in a supporting inequality and the unprojected OSD update gives

\[
x_{t+1}=x_t-\eta g_t,\qquad [g_t]=\frac{[\ell]}{[x]},\qquad
[x_t]=[\eta][g_t],\qquad [\eta]=\frac{[x]^2}{[\ell]}.
\]

The source explicitly chooses \(V=\mathbb R^d\) for this update calculation. It then says the learning rate is not unitless and must depend on problem characteristics. The ratio identity is literal; the categorical non-unitless sentence is separately flagged below because special dimensional cancellations are not excluded in the text.

The sanity-check display is

\[
\sum_{t=1}^T(\ell_t(x_t)-\ell_t(u))
\le \frac{\|u-x_1\|_2^2}{2\eta}
  +\frac\eta2\sum_{t=1}^T\|g_t\|_2^2.
\]

The source checks the left side and both right-side terms have unit \([\ell]\):

\[
\left[\frac{\|u-x_1\|_2^2}{\eta}\right]
=\frac{[x]^2}{[\eta]}=[\ell],\qquad
\left[\eta\sum_{t=1}^T\|g_t\|_2^2\right]
=[\eta][g_t]^2=[\ell].
\]

The numerical factors \(1/2\) remain in the inequality; they are omitted only from unit calculations because they are dimensionless. Summation over rounds adds no unit of continuous time. This sanity check does not establish numerical correctness or scale invariance of a regret bound by itself.

For the concrete example, \(x_t\) is measured in meters, \(x'_t=x_t/1000\) in kilometers, and the numerical schedule is \(\eta=1/\sqrt T\). Loss values and their units are held fixed. The transformed loss is the composite \(z\mapsto\ell_t(1000z)\), not an unchanged numerical function of the new coordinate. At corresponding points the source writes

\[
g'_t=\nabla_{x'}\ell_t(1000x'_t)
 =1000\nabla_x\ell_t(x_t)=1000g_t.
\]

Using the same numerical rate gives

\[
x'_{t+1}=\frac{x_t}{1000}-\frac{1000}{\sqrt T}g_t,
\qquad
1000x'_{t+1}=x_t-\frac{1000^2}{\sqrt T}g_t.
\]

The second equation is written with \(x_{t+1}\) on the left in the source. Here it is disambiguated as the **converted new update**, while the source's exact notation is retained in inventory N22.02 and page pixels. It is not an equality between the original algorithm next state and the new algorithm next state. The author says the effective learning rate changes by one million and warns that the path will change drastically. The final paragraph prescribes a rate multiplier

\[
(1/1000)^2=1/1000000
\]

when changing from meters to kilometers, since loss units stay fixed and \([\eta]=[x]^2/[\ell]\).

## Necessary context, quantifiers and feedback semantics

Algorithm2.2 has a nonempty closed convex \(V\subseteq\mathbb R^d\), initial \(x_1\in V\), positive rates \(\eta_1,\ldots,\eta_T\), and finite rounds \(1,\ldots,T\). Each round outputs \(x_t\), incurs the loss, selects \(g_t\in\partial\ell_t(x_t)\), and projects \(x_t-\eta_tg_t\). This is subgradient access after play. No bandit-only feedback, probability law, filtration, random stopping rule or high-probability guarantee is introduced here. The paragraph about density units is a dimensional illustration, not a stochastic assumption of OSD.

The unit example specializes to \(V=\mathbb R^d\), so no projected-domain transport theorem is used. Its chain-rule line uses gradients and requires differentiability at the corresponding points, although the enclosing algorithm permits subgradients. Definition2.20 uses a proper extended-real function and the supporting inequality for every point \(y\in\mathbb R^d\); actual loss evaluations must be finite to interpret numerical loss differences and units. Printed17 explicitly warns subgradients need not be unique. Thus a claim about all independently selected subgradients in two runs is stronger than the example.

The regret comparator is any fixed \(u\in V\); the source does not require an optimal comparator to exist. Its constant \(\eta\) is held across the finite horizon. The particular \(1/\sqrt T\) expression needs \(T>0\) and knowledge of that horizon for its use. An arbitrary conversion factor, simultaneous loss-output rescaling, heterogeneous coordinate units, time-dependent unit changes, or general matrix transformation is not a literal claim of this example. When describing an optional generalization, keep the direction explicit: if \(x'=x/k\) with \(k>0\), the concrete source corresponds to \(k=1000\); the corresponding gradient factor is \(k\) and rate factor \(k^{-2}\). This is a proposed extension convention, not an extracted arbitrary-k theorem.

A one-step statement begins at corresponding current positions. A full matched-path claim also needs corresponding initial states, transformed losses at every round, and appropriately corresponding feedback/oracle choices. Once incorrectly tuned runs diverge, the gradient of one old trajectory cannot be reused as the gradient along the new trajectory. Each run evaluates its own loss derivative at its own iterate. No full trajectory induction or regret-value transport is printed in this subsection.

## Negative terminal residual: preserve two different source displays

Theorem2.13 on printed13 and its direct telescope on printed14 contain

\[
\operatorname{Reg}_T(u)\le
\frac{\|u-x_1\|_2^2}{2\eta}
+\frac\eta2\sum_{t=1}^T\|g_t\|_2^2
-\frac{\|x_{T+1}-u\|_2^2}{2\eta}.
\]

Theorem2.13's original statement uses differentiable convex losses on an open set containing \(V\); Section2.2.2 states why its proof transfers to subgradients via the supporting inequality, and Lemma2.31 supplies the OSD one-step inequality. Printed14 explicitly says the last term is nonpositive and usually dropped, while warning it matters in advanced proofs. Printed21 intentionally displays the relaxed two-term bound for its unit check. Preserve both facts. Do not silently rewrite the literal sanity-check display to include a term it does not show, and do not erase that term from the earlier full theorem. Constant-rate initial-distance bounds can hold on unbounded domains; finite diameter is not needed for the unprojected unit example.

A dimensional check of the omitted residual or an invariance theorem for the full bound would be a separately identified extension. It would require corresponding comparator and terminal iterate, not merely a scalar coefficient identity. The displayed unit calculation does not prove optimization of actual regret or the stronger bound.

## Complete bounded region inventory

Regions refer to y fractions from the top of the full-page render, with textual locators disambiguating adjacent displays. Page headers, numbers and whitespace are excluded globally as furniture. Every substantive paragraph/display in subsection2.2.3 is a NODE; neighboring read regions are explicitly included or excluded below.

- **X13.01 — EXCLUDED**, printed13/PDF25, top through projection-proof end, y0.15-0.24: Tail of projection proof. Exclusion reason: Projection proof is outside unit-analysis target; Algorithm2.2 supplies the update as a boundary input.
- **N13.01 — NODE**, printed13/PDF25, Lemma2.12 and display, y0.26-0.39: Nonempty closed convex V in R^d; convex differentiable loss on open set containing V; eta_t>0; g_t=grad ell_t(x_t); x_(t+1)=Pi_V(x_t-eta_t g_t). For all u in V, eta_t(ell_t(x_t)-ell_t(u)) <= eta_t<g_t,x_t-u> <= (||x_t-u||²-||x_(t+1)-u||²)/2 + eta_t²||g_t||²/2. Context only: one-step origin of endpoint term.
- **X13.02 — EXCLUDED**, printed13/PDF25, Lemma2.12 proof, y0.41-0.56: Projection/convexity proof citing Proposition2.11 and Theorem2.7. Exclusion reason: Earlier proof leaves are not expanded by this bounded unit-analysis extraction.
- **N13.02 — NODE**, printed13/PDF25, Theorem2.13 first clause, y0.59-0.73: V nonempty closed convex, diameter D=sup_(x,y in V)||x-y||; arbitrary sequence ell_1,...,ell_T convex and differentiable on an open set containing V; any x_1 in V; printed 0<eta_(t+1)<=eta_t for t=1,...,T-1. For all u in V, Reg_T(u)<=D²/(2eta_T)+sum_(t=1)^T eta_t||g_t||²/2-||x_(T+1)-u||²/(2eta_T). This is context; the fixed-rate clause below supplies the bound used in unit analysis.
- **N13.03 — NODE**, printed13/PDF25, Theorem2.13 moreover clause, y0.75-0.82: If eta_t=eta for every t=1,...,T, then for every u in V: Reg_T(u)<=||u-x_1||²/(2eta)+(eta/2)sum_(t=1)^T||g_t||²-||x_(T+1)-u||²/(2eta). The source retains the negative terminal residual.
- **N13.04 — NODE**, printed13/PDF25, last proof sentence y0.83-0.85: Divide Lemma2.12 by eta_t and sum over t=1,...,T. Division uses positive learning rates.
- **X14.01 — EXCLUDED**, printed14/PDF26, first five-line proof display y0.15-0.39: Time-varying reciprocal-difference rearrangement, diameter replacement and telescoping proof. Exclusion reason: Not needed for constant-rate unit check; constant-rate proof is separately retained, so bounded diameter is not silently imported.
- **N14.01 — NODE**, printed14/PDF26, constant-rate proof display y0.40-0.50: For constant eta, sum_t (||x_t-u||²-||x_(t+1)-u||²)/(2eta)+(eta/2)sum_t||g_t||² telescopes to ||x_1-u||²/(2eta)-||x_(T+1)-u||²/(2eta)+(eta/2)sum_t||g_t||².
- **N14.02 — NODE**, printed14/PDF26, first observation y0.53-0.59: Squared-gradient terms arise because x_t is output before ell_t is known. Source contrasts observing loss first and cites Section15.5.1; that cited result is a boundary leaf, not proved here.
- **N14.03 — NODE**, printed14/PDF26, second observation y0.59-0.63: The constant-rate bound holds even for D=infinity; the first term depends on initial distance from comparator u. No bounded-diameter hypothesis is needed for this fixed-comparator expression.
- **N14.04 — NODE**, printed14/PDF26, third observation y0.63-0.66: The final term in both bounds is nonpositive and usually discarded; source warns that advanced proofs sometimes require it. This justifies the relaxed two-term display on printed21, not deletion from the original theorem.
- **X14.02 — EXCLUDED**, printed14/PDF26, fourth observation y0.66-0.74: Time-varying rates, bounded-domain difficulty, Section5.2 and stochastic Chapter3 contrast. Exclusion reason: Separate time-varying-rate question, not a proof of coordinate-unit transport.
- **X14.03 — EXCLUDED**, printed14/PDF26, fifth observation y0.75-0.79: Regret analysis guides learning-rate choice. Exclusion reason: General motivation outside the selected dimensional derivation.
- **X14.04 — EXCLUDED**, printed14/PDF26, last paragraph y0.80-0.86: Transition to optimizing constant learning rate for fixed iteration count. Exclusion reason: Scalar optimizer calculation is a separate target; no optimizer theorem is extracted here.
- **X16.01 — EXCLUDED**, printed16/PDF28, top Huber example through y0.36: Huber loss, gradient, constant learning rate and fixed-predictor asymptotic example. Exclusion reason: Separate example, unnecessary for meter/kilometer coordinate calculation.
- **N16.01 — NODE**, printed16/PDF28, Section2.2 introduction y0.39-0.50: Transition from differentiable convex losses to nondifferentiable convex losses by replacing gradients with subgradients; examples absolute and hinge loss. Context for distinguishing OSD from the differentiable meter/kilometer example.
- **X16.02 — EXCLUDED**, printed16/PDF28, Definition2.16, paragraph, Example2.17 y0.55-0.66: Closed function, lower semicontinuity equivalence/citation, closed indicator example. Exclusion reason: Closed-function theory is not used by this bounded unit derivation.
- **N16.02 — NODE**, printed16/PDF28, Definition2.18 y0.67-0.70: Proper means nowhere -infinity and finite somewhere. The subsequent prose says the book mainly studies convex proper functions. This types Definition2.20, not an extra new unit-scaling hypothesis.
- **X16.03 — EXCLUDED**, printed16/PDF28, Example2.19 y0.74-0.76: Indicator function proper iff its set is nonempty. Exclusion reason: Separate example, not used in the unit calculation.
- **N16.03 — NODE**, printed16/PDF28, Definition2.20/display y0.79-0.85: For a proper f:R^d→(-infinity,+infinity], g in R^d is a subgradient at x if f(y)>=f(x)+<g,y-x> for every y in R^d. The supporting inequality supplies loss divided by coordinate units for g; actual algorithm points must have finite meaningful losses.
- **N17.01 — NODE**, printed17/PDF29, first paragraph y0.15-0.21: A subgradient need not be unique; the set is denoted partial f(x), the subdifferential. Subdifferentiable at x means partial f(x) is nonempty. Therefore arbitrary independent oracle choices cannot be silently identified across runs.
- **X17.01 — EXCLUDED**, printed17/PDF29, domain/interior paragraph and footnote y0.21-0.28 and footnote: Domain of subdifferential, nonempty interior subdifferentials and Rockafellar1970 Theorem23.4, relative-interior footnote. Exclusion reason: Existence theory is a boundary context, not needed after Algorithm2.2 explicitly selects a subgradient.
- **X17.02 — EXCLUDED**, printed17/PDF29, Theorem2.21 and proof y0.29-0.55: Subgradients everywhere imply convexity; supporting inequalities proof. Exclusion reason: Separate convexity characterization, not a coordinate transport proof.
- **N17.02 — NODE**, printed17/PDF29, differentiability paragraph/Theorem2.22 y0.56-0.62: For convex f finite at x, differentiability at x is equivalent to partial f(x) being a singleton whose element is grad f(x); cited Rockafellar1970 Theorem25.1. This is a boundary source leaf connecting subgradient and gradient language; its cited proof is not reproduced.
- **X17.03 — EXCLUDED**, printed17/PDF29, Theorem2.23 and proof start y0.63-0.81: Subdifferential sum rule and proof. Exclusion reason: No sum-rule transport is used in the selected dimensional example.
- **X19.01 — EXCLUDED**, printed19/PDF31, intro/Definition2.29/Theorem2.30 and proof y0.15-0.47: Lipschitz definition, gradient norm equivalence and proof. Exclusion reason: Unit analysis motivates retaining L but does not rely on this Lipschitz theorem for the scale calculation.
- **X19.02 — EXCLUDED**, printed19/PDF31, nondifferentiability example y0.48-0.54: Convex function |x_1| on R² nondifferentiable on a segment. Exclusion reason: Separate illustration, not an input to coordinate-unit scaling.
- **N19.01 — NODE**, printed19/PDF31, Section2.2.2 paragraph/display y0.60-0.75: The only gradient property used for Theorem2.13 is ell_t(x_t)-ell_t(u)<=<g_t,x_t-u>. This also holds for g_t in partial ell_t(x_t), so the source says the same regret bound holds after replacing differentiability with subdifferentiability and gradients with subgradients. This is the source bridge for invoking Theorem2.13 in the OSD unit check.
- **N19.02 — NODE**, printed19/PDF31, Lemma2.31 and display y0.76-0.84: V nonempty closed convex subset R^d; ell_t:R^d→(-infinity,+infinity] subdifferentiable on V; eta_t>0; g_t in partial ell_t(x_t), x_(t+1)=Pi_V(x_t-eta_t g_t). For every u in V, eta_t(ell_t(x_t)-ell_t(u))<=eta_t<g_t,x_t-u><=||x_t-u||²/2-||x_(t+1)-u||²/2+eta_t²||g_t||²/2.
- **N20.01 — NODE**, printed20/PDF32, Algorithm2.2 requirement line y0.17-0.19: Nonempty closed convex V subset R^d, x_1 in V, eta_1,...,eta_T>0. Horizon is the finite loop count T.
- **N20.02 — NODE**, printed20/PDF32, Algorithm2.2 lines1-6 y0.19-0.28: For t=1,...,T: output x_t in V; pay ell_t(x_t), where ell_t is subdifferentiable on V; choose g_t in partial ell_t(x_t); set x_(t+1)=Pi_V(x_t-eta_t g_t)=argmin_(y in V)||x_t-eta_t g_t-y||_2. Full-information subgradient access follows the play, not bandit scalar-only feedback.
- **N20.03 — NODE**, printed20/PDF32, post-algorithm paragraph y0.30-0.33: The source says OSD differs from Algorithm2.1 only at line4, substituting selected subgradient for gradient. Algorithm2.1 is a boundary citation; no independent second algorithm is reconstructed here.
- **X20.01 — EXCLUDED**, printed20/PDF32, Example2.32 introduction/display/rate y0.35-0.49: Absolute-loss guessing game; subdifferential {1},[-1,1],{-1}; optimal-rate O(sqrt(T)) regret. Exclusion reason: Separate example preceding the subsection. It does not prove unit conversion; all its pixels/text retained.
- **N20.04 — NODE**, printed20/PDF32, Section2.2.3 heading and first paragraph y0.53-0.63: Actual target begins here: Unit Analysis Bits. Source warns that setting problem constants such as Lipschitz L to1 hides information needed to check equations and implement algorithms correctly.
- **N20.05 — NODE**, printed20/PDF32, physical-units paragraph y0.63-0.72: Assign units such as meters/seconds/Joules. A physically meaningful equation must have equal units on both sides; quantities of incompatible units cannot be added.
- **N20.06 — NODE**, printed20/PDF32, symbolic units paragraph y0.72-0.79: The same dimensional sanity check is proposed for online learning: [x] denotes prediction units and [ell] loss units; terms combined in a formula must have matching units.
- **N20.07 — NODE**, printed20/PDF32, last lines continued onto printed21 y0.79-0.84: Transcendental functions take unitless arguments; logarithms/exponentials can act on ratios with matching units to yield unitless quantities. This is physical dimensional interpretation, not a prohibition on real-valued analytic functions.
- **N21.01 — NODE**, printed21/PDF33, continuation top y0.15-0.19: Probabilities are unitless; probability density has reciprocal units of the represented random variable because it is probability per unit. Contextual rule only; no probability model enters the subsequent deterministic OSD calculation.
- **N21.02 — NODE**, printed21/PDF33, next paragraph y0.20-0.25: Source says a unit mismatch indicates an incorrect equation or a hidden unit-bearing constant, and uses dimensional analysis to constrain dependence on problem quantities.
- **N21.03 — NODE**, printed21/PDF33, OSD paragraph y0.26-0.33: Specialize Algorithm2.2 to V=R^d: x_(t+1)=x_t-eta g_t. Coherence requires eta g_t and x_t to have the same units. The same scalar learning rate is used in this displayed update.
- **N21.04 — NODE**, printed21/PDF33, subgradient-unit display y0.34-0.37: From the subgradient definition the source asserts [g_t]=[ell]/[x]. Coordinates are assigned a common symbolic unit; heterogeneous coordinate scaling is not discussed.
- **N21.05 — NODE**, printed21/PDF33, consistency sentence y0.38-0.41: [x_t]=[eta g_t]=[eta][g_t]. Products and quotients of symbolic units follow the displayed multiplicative convention.
- **N21.06 — NODE**, printed21/PDF33, learning-rate-unit display y0.41-0.45: [eta]=[x]/[g_t]=[x]/([ell]/[x])=[x]^2/[ell]. This is the exact dimensional relation, not a uniquely selected numerical learning rate.
- **N21.07 — NODE**, printed21/PDF33, interpretation paragraph y0.46-0.49: Source states that the learning rate is not a unitless quantity and must depend on problem characteristics in a certain way, even before a regret guarantee is derived. The categorical unitless wording is preserved as literal claim; special dimensional cancellations are a separate qualification.
- **N21.08 — NODE**, printed21/PDF33, regret intro/display y0.50-0.57: Source attributes constant-rate OSD bound to Theorem2.13: sum_(t=1)^T(ell_t(x_t)-ell_t(u)) <= ||u-x_1||_2²/(2eta)+(eta/2)sum_(t=1)^T||g_t||_2². This is the relaxed bound; full theorem retains a negative endpoint term. Comparator quantification is inherited from the theorem, for each u in V.
- **N21.09 — NODE**, printed21/PDF33, LHS units paragraph y0.58-0.61: The left side is a sum of losses and has unit [ell]; check each right-side term has that same unit. T and numerical constants are dimensionless counts/scalars.
- **N21.10 — NODE**, printed21/PDF33, first-term dimensional display y0.62-0.67: [||u-x_1||_2²/eta]=[x]²/[eta]=[x]²/([x]²/[ell])=[ell]. Factor2 is numerically present in the bound but unitless, so omitted only inside the unit calculation.
- **N21.11 — NODE**, printed21/PDF33, second-term intro/display y0.67-0.71: [eta sum_(t=1)^T||g_t||_2²]=[eta][g_t]²=([x]²/[ell])([ell]²/[x]²)=[ell]. Summands share the same unit; summation does not add a time unit.
- **N21.12 — NODE**, printed21/PDF33, meter example intro y0.72-0.78: Hidden units cause implementation problems. Let x_t represent a location in meters; choose eta=1/sqrt(T). Change measurement to kilometers: x_prime_t=x_t/1000. This retains physical location and loss-value units. The formula requires positive finite horizon for a positive finite rate.
- **N21.13 — NODE**, printed21/PDF33, same-problem/invariance sentences y0.78-0.81: Source says the underlying learning problem is identical because this is only a change of units, and algorithm behavior should be invariant. This expresses physical coordinate invariance, not equality of numerical coordinate vectors.
- **N21.14 — NODE**, printed21/PDF33, last displayed inline equation y0.82-0.84: At corresponding points the source writes g_prime_t=grad_(x_prime) ell_t(1000 x_prime_t)=1000 grad_x ell_t(x_t)=1000 g_t. This example uses gradients despite the enclosing OSD discussion. The transformed loss function is z↦ell_t(1000z), with loss outputs unscaled.
- **N22.01 — NODE**, printed22/PDF34, first sentence/formula y0.15-0.18: Reuse the numerically unchanged eta=1/sqrt(T): x_prime_(t+1)=x_prime_t-eta g_prime_t=x_t/1000-(1/sqrt(T))(1000g_t). This calculation begins at corresponding current points.
- **N22.02 — NODE**, printed22/PDF34, convert-back sentence/formula y0.18-0.20: Multiplying the new iterate by1000 gives the source displayed x_(t+1)=x_t-(1000²/sqrt(T))g_t. The unprimed x_(t+1) here names the converted NEW update; it must not be silently equated with the original algorithm update using eta.
- **N22.03 — NODE**, printed22/PDF34, first paragraph conclusion y0.20-0.23: Source says effective rate is multiplied by one million and this will drastically change the algorithm path because of a unit change. Algebra fixes the multiplier; universal strict/quantitative path change requires separate nondegeneracy qualifications.
- **N22.04 — NODE**, printed22/PDF34, second paragraph start y0.24-0.26: Source attributes failure to the hidden-unit constant in the learning rate and says the rate must change when coordinate units change.
- **N22.05 — NODE**, printed22/PDF34, last subsection sentence y0.26-0.29: Correct eta has units [x]²/[ell] and should be scaled by (1/1000)²=1/1000000 when switching meters to kilometers. Loss units are held fixed. The source does not display a full trajectory induction or transformed regret theorem here.
- **X22.01 — EXCLUDED**, printed22/PDF34, Section2.3 first pointwise inequality y0.33-0.39: Convex loss supporting inequality for every u in V. Exclusion reason: Starts separate linear-regret reduction; supporting inequality needed here is already retained from Definition2.20/Section2.2.2.
- **X22.02 — EXCLUDED**, printed22/PDF34, Section2.3 summed inequality y0.40-0.47: Sum supporting inequalities over time. Exclusion reason: Separate linear-regret proof.
- **X22.03 — EXCLUDED**, printed22/PDF34, linear losses definition and comparison y0.48-0.55: Define linear losses ell_t_tilde(x)=<g_t,x>; compare regrets. Exclusion reason: Separate reduction, not needed for unit-scaling.
- **X22.04 — EXCLUDED**, printed22/PDF34, interpretation paragraph y0.55-0.64: OCO-to-linear reduction, caution using Example2.14, optimality motivation. Exclusion reason: No scale-equivariance guarantee is supplied by this paragraph.
- **X22.05 — EXCLUDED**, printed22/PDF34, OLO definition/display y0.64-0.74: Linear regret for arbitrary vectors g_1,...,g_T in R^d and every u in V; named OLO. Exclusion reason: Separate online-linear setting, not a license to freeze gradients across transformed nonlinear-loss paths.
- **X22.06 — EXCLUDED**, printed22/PDF34, Section2.4 history y0.78-0.85: Shor1964 generalized gradients and Rockafellar1963 subgradient calculus origins. Exclusion reason: Historical attribution outside selected derivation.
- **X23.01 — EXCLUDED**, printed23/PDF35, history continuation first paragraph y0.15-0.20: Zinkevich2003 and Gordon1999 OCO history. Exclusion reason: Neighboring locator context only.
- **X23.02 — EXCLUDED**, printed23/PDF35, second history paragraph y0.21-0.28: Online-learning/subgradient history and citations. Exclusion reason: No unit-scaling derivation.
- **X23.03 — EXCLUDED**, printed23/PDF35, bounded-domain discussion and display y0.29-0.55: Comparator versus best-in-hindsight minimizer convention, unbounded domains, FTRL/Chapter7 and Example3.2. Exclusion reason: Relevant general caution but not needed to prove unit conversion; fixed-comparator context already retained from Theorem2.13.
- **X23.04 — EXCLUDED**, printed23/PDF35, Problem2.1 in y0.61-0.84: Exercise2.1: harmonic square-root sum. Exclusion reason: Exercise outside selected Unit Analysis Bits target.
- **X23.05 — EXCLUDED**, printed23/PDF35, Problem2.2 in y0.61-0.84: Exercise2.2: time-varying learning-rate regret. Exclusion reason: Exercise outside selected Unit Analysis Bits target.
- **X23.06 — EXCLUDED**, printed23/PDF35, Problem2.3 in y0.61-0.84: Exercise2.3: epsilon-insensitive subdifferential. Exclusion reason: Exercise outside selected Unit Analysis Bits target.
- **X23.07 — EXCLUDED**, printed23/PDF35, Problem2.4 in y0.61-0.84: Exercise2.4: Euclidean norm subdifferential. Exclusion reason: Exercise outside selected Unit Analysis Bits target.
- **X23.08 — EXCLUDED**, printed23/PDF35, Problem2.5 in y0.61-0.84: Exercise2.5: OSD versus FTL example. Exclusion reason: Exercise outside selected Unit Analysis Bits target.

## Proposed source topology

Edges point from inputs to consumers. Context and warning nodes are not automatically AND proof premises.

- **E01**: N16.03 AND N20.05 AND N20.06 → N21.04. Use-site: printed21 subgradient-unit display. Use supporting inequality dimensions: loss difference and inner product have matching units. Common coordinate unit and symbolic unit algebra are implicit; G18.01 remains.
- **E02**: N20.01 AND N20.02 → N21.03. Use-site: printed21 first OSD paragraph. Explicitly specialize V=R^d, removing projection; retain positive step, finite horizon and play-before-feedback order.
- **E03**: N21.03 AND N20.05 AND N20.06 → N21.05. Use-site: printed21 update-consistency sentence. The difference of coordinates must have coordinate units. No numeric rate or convergence assertion follows.
- **E04**: N21.04 AND N21.05 → N21.06. Use-site: printed21 learning-rate-unit display. Substitute [g_t]=[ell]/[x] into [eta]=[x]/[g_t]. Dimensional algebra only.
- **E05**: N21.06 AND G18.05 → N21.07. Use-site: printed21 sentence after unit display. Preserve author interpretation; the categorical non-unitless claim requires separate treatment of special dimensional cancellation.
- **E06**: N13.01 AND N13.04 AND N14.01 → N13.03. Use-site: Theorem2.13 constant-rate clause and printed14 proof. Positive constant eta enables summation and division, telescoping distances. Endpoint remains; no bounded-diameter substitution is used.
- **E07**: N13.03 AND N19.01 AND N14.04 → N21.08. Use-site: printed21 constant-rate OSD sanity-check display. Source explicitly transfers gradient proof via supporting inequality to selected subgradients; discard nonpositive terminal residual only for displayed relaxed bound. Comparator is fixed arbitrary u in V.
- **E08**: N21.08 AND N20.06 → N21.09. Use-site: printed21 LHS-units prose. All loss values use the same output unit; finite summation and numerical constants are dimensionless.
- **E09**: N21.06 AND N21.08 AND N21.09 → N21.10. Use-site: printed21 first-term unit display. Comparator and initial point share [x]. Numerical factor2 is omitted only from unit notation, retained in the inequality.
- **E10**: N21.04 AND N21.06 AND N21.08 AND N21.09 → N21.11. Use-site: printed21 second-term unit display. Use common gradient unit across rounds and unitless finite count T. This is dimensional consistency, not a new regret proof.
- **E11**: N21.12 AND N21.13 AND G18.02 → N21.14. Use-site: printed21 last line. Transform the loss to z↦ell_t(1000z), keep its output units fixed, differentiate at corresponding x=1000x_prime. Differentiable example or separate subgradient transport is required; independent arbitrary subgradient selections are not discharged.
- **E12**: N21.03 AND N21.12 AND N21.14 AND G18.06 → N22.01. Use-site: printed22 first sentence. Use positive finite T and same numerical eta in both coordinate systems; current positions correspond before this update.
- **E13**: N22.01 → N22.02. Use-site: printed22 convert-back sentence. Multiply new coordinate by1000. Reused unprimed next-state notation denotes converted new run, not proof that it equals original next state.
- **E14**: N22.02 AND G18.03 AND G18.04 → N22.03. Use-site: printed22 first paragraph conclusion. The multiplier1000² is exact. Path-level and universal strict change need explicit feedback coupling/nonzero conditions; no induction or quantitative divergence is printed.
- **E15**: N21.06 AND N21.12 AND N21.13 AND N22.04 → N22.05. Use-site: printed22 last subsection paragraph. Prediction unit changes by1/1000 while loss unit stays fixed, so ratio unit changes by1/1000000. Printed source supplies dimensional explanation, not full path transport proof.

Only one unit-analysis chain and one concrete coordinate computation are printed. The dimensional derivation, local update identity, and a full path theorem have different conclusions; they are not falsely labelled interchangeable OR proofs. For the background OSD relaxed bound only, the source's proof-transfer route and the optional direct Lemma2.31 telescope can be represented as **(transfer AND endpoint discard) OR (positive-rate direct sum AND telescope AND endpoint discard)**. The second is a proposed source-supported composition, not an additional printed proof. Independent review must approve its inclusion.

## Source gaps and mathematical qualifications

These records preserve what the source says and identify what is missing. They are not approved repairs, not implementation-driven weakenings, and not SOURCE_INVALID verdicts.

### G18.01 — SOURCE_GAP-dimensional-formalization

Use-site: N21.04-N21.07. Literal source: Symbolic units satisfy displayed product/quotient identities.

Missing detail: No formal space of units, equality semantics, or theorem distinguishing physical dimension from numerical coordinates is defined. Numeric step-size uniqueness or scale-factor selection does not follow merely from dimensional consistency.

Separate qualification: A dimensional algebra can be specified separately; it is not a hidden source theorem.

### G18.02 — SOURCE_GAP-regularity-and-oracle-transport

Use-site: N21.14. Literal source: The example writes a gradient chain-rule equality.

Missing detail: The surrounding OSD setting permits nonsmooth losses, but this line needs differentiability at corresponding points or a separately established subgradient-set transport. Arbitrary selected subgradients need not be corresponding selections.

Separate qualification: Keep gradient example distinct from general subgradient transport and deterministic/stochastic oracle coupling.

### G18.03 — SOURCE_GAP-trajectory-correspondence

Use-site: N22.01-N22.05. Literal source: Expected invariant behavior and corrected eta scaling are stated; changed effective rate is calculated locally.

Missing detail: No full induction is printed for paired runs with matching initial points, transformed loss sequence, and corresponding feedback. After divergence, old-run g_t cannot be reused as the gradient of the new run without justification.

Separate qualification: At paired points x_prime=x/1000 the one-step formula is exact; a full path theorem must state all coupling hypotheses and recompute feedback at each own iterate.

### G18.04 — SOURCE_GAP-nondegeneracy-of-path-change

Use-site: N22.03. Literal source: Effective rate changes by one million and will drastically change the path.

Missing detail: No quantitative lower bound or nonzero-gradient premise is given. Zero feedback can produce identical paths despite the changed effective rate; no universal strict mismatch follows from the coefficient multiplier alone.

Separate qualification: Preserve the literal warning while separating potential/generic failure from an always-different theorem. No source-invalidity verdict is issued by extractor.

### G18.05 — SOURCE_GAP-unitless-special-case

Use-site: N21.07. Literal source: The learning rate is not a unitless quantity.

Missing detail: The displayed identity [eta]=[x]²/[ell] permits cancellation when [ell]=[x]². The text does not exclude that special unit convention.

Separate qualification: Do not replace the literal claim silently. A separate qualified reading is that eta carries the ratio unit and cannot be assumed universally unitless across arbitrary problem units.

### G18.06 — SOURCE_GAP-horizon-and-domain-boundaries

Use-site: N21.12-N22.05. Literal source: eta=1/sqrt(T), meter/kilometer positive scale1000.

Missing detail: Positive finite T is implicit; T=0 does not define a finite positive numerical rate in ordinary arithmetic. Zero/negative conversion factors and arbitrary heterogeneous transforms are not part of this physical example.

Separate qualification: Any broader formal totalized or arbitrary-scale statement must be identified as an extension, not silently attributed to the source.

## Separate proposed specification/repair layer

- P1: If a formal unit algebra is desired, specify its operations and the distinction between unit dimension and numerical coordinate representation. Preserve the literal ratio relation. Treat the special dimensionless case separately rather than silently changing the source sentence.
- P2: For a full coordinate-path statement, explicitly pair loss sequences by composition, pair initial states and choose corresponding gradients or subgradients. Define the converted new path separately from the original path. Keep the unprojected domain unless projection transport is separately proved.
- P3: State positive finite horizon for the illustrative rate. Preserve the source's concrete positive factor1000; label arbitrary positive scale, loss scaling or matrix scaling as generalization.
- P4: A strict failure witness needs nonzero feedback or another explicit nondegeneracy condition. A millionfold coefficient change alone is not a universal quantitative separation of trajectories. Keep the original warning visible while reviewing a precise replacement independently.
- P5: Any full-bound transport must preserve the terminal residual and comparator semantics. The source's relaxed sanity-check display stays attributed exactly as shown.

No proposed item is approved here. The next reviewer should inspect the raw pinned pages and this public extraction/topology without implementation Lean or private extractor reasoning, checking missing regions, gradients versus subgradients, scale direction, endpoint treatment, path feedback, special cases and AND/OR logic.
