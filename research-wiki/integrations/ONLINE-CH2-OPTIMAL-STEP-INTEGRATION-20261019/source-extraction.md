# Batch 17 source-only extraction: stepsize minimization

Status: EXTRACTED / TOPOLOGY PROPOSED / INDEPENDENT REVIEW PENDING. The extractor does not approve this topology. This is not a theorem-completion, source-invalidity, Lean-compilation, or publication verdict.

## Frozen scientific input

- Francesco Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*, arXiv:1912.13213v10, 21 June 2026 (title-page text verified).
- Original file: `private-location-sha256:5c1f5e5e81846c7e88e07a27b0920036f425e35de250cc342f2e117596bd2114`.
- Original SHA256: `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`.
- Target: the unnumbered minimization discussion in Section 2.1, printed p.15 = PDF page 27 (one-based). Equation (2.1) numbers the resulting regret bound, not a separate minimization theorem.
- Primary context: printed pp.14–16 = PDF pages 26–28. Printed p.13 = PDF page 25 was added solely because p.14 begins inside the proof of Theorem 2.13 and its assumptions are necessary.
- `source-page-025.png` through `source-page-028.png` are complete Poppler-rendered page images, inspected by the extractor. They retain margins, page numbers, formulas, warnings, citations, and adjacent examples. Coordinates below are approximate normalized image rectangles `[left,top,right,bottom]`, origin top-left. The full pages, not coordinates alone, are the authoritative locator.
- Raw text is in `source-printed13-pdf25.txt`, `source-printed14-16-pdf26-28.txt`, and `source-title-pdf01.txt`. Text extraction scrambles some equation layout. The transcriptions below were checked against the page images.
- No implementation Lean, PR descriptions, previous mathematical verdicts, or batch16 scientific material was consulted. Protocol documents are governance inputs only. No scientific memory or external mathematical source was used.

## Scope and notation

The bounded root is the p.15 scalar stepsize calculation, with its OGD regret context and feasibility warnings. This packet does not recursively extract the entire proof of Theorem 2.13, Algorithm 2.1, projection theory, Chapter 5 lower bounds, or later adaptive algorithms. Named dependencies outside the boundary are visible source leaves, not silently certified facts.

For compact transcription only, write

\[
R=\|u-x_1\|_2,\qquad S=\sum_{t=1}^T\|g_t\|_2^2,
\qquad \operatorname{Reg}_T(u)=\sum_{t=1}^T(\ell_t(x_t)-\ell_t(u)).
\]

The symbols `R`, `S`, and `Reg` are extraction abbreviations, not new source definitions. The source uses Euclidean norms, gradients \(g_t=\nabla\ell_t(x_t)\), a fixed comparator \(u\in V\), and a finite iteration count \(T\). It does not take an expectation or assert a high-probability event in this calculation.

## Literal source inventory

Each substantive paragraph/display in the primary pp.14–16 window is assigned NODE or EXCLUDED below. Subdivision of a displayed chain exposes each material step. The p.13 extension is also inventoried. NODE means inclusion in this proposed source account, not mathematical approval.

### Printed 13 / PDF 25: necessary premise extension

| ID | Region | Disposition and source content |
|---|---|---|
| X13.01 | top [0.21,0.15,0.86,0.24] | EXCLUDED: trailing projection-proof paragraph/display predates the bounded extraction. Its cited result remains the explicit leaf N13.04; no full projection proof is claimed. |
| N13.01 | [0.21,0.26,0.86,0.39] | NODE: transition to one-iteration regret and Lemma 2.12. \(V\subseteq\mathbb R^d\) nonempty, closed, convex; \(\ell_t\) convex and differentiable on an open set containing \(V\); \(\eta_t>0\); \(g_t=\nabla\ell_t(x_t)\), \(x_{t+1}=\Pi_V(x_t-\eta_tg_t)\); conclusion for every \(u\in V\). |
| N13.02 | same display | NODE: \(\eta_t(\ell_t(x_t)-\ell_t(u))\le\eta_t\langle g_t,x_t-u\rangle\le\frac12\|x_t-u\|_2^2-\frac12\|x_{t+1}-u\|_2^2+\frac{\eta_t^2}{2}\|g_t\|_2^2\). |
| N13.03 | [0.21,0.41,0.86,0.54] | NODE: proof invokes Proposition 2.11 and Theorem 2.7; projection inequality, expansion with cross term \(-2\eta_t\langle g_t,x_t-u\rangle\), then convexity and rearrangement give N13.02. |
| N13.04 | citations in N13.03 | NODE / BOUNDARY_SOURCE_LEAF: Proposition 2.11 and Theorem 2.7, cited by source as the projection and convexity inputs. Complete statements/proofs are not extracted here. |
| N13.05 | [0.21,0.56,0.86,0.73] | NODE: Theorem 2.13. \(V\subseteq\mathbb R^d\) nonempty, closed, convex with \(D:=\sup_{x,y\in V}\|x-y\|_2\); arbitrary sequence \(\ell_1,\ldots,\ell_T\) convex/differentiable on an open set containing \(V\); any \(x_1\in V\); source prints \(0<\eta_{t+1}\le\eta_t\), \(t=1,\ldots,T-1\). For every \(u\in V\), \(\operatorname{Reg}_T(u)\le D^2/(2\eta_T)+\sum_{t=1}^T(\eta_t/2)\|g_t\|_2^2-\|x_{T+1}-u\|_2^2/(2\eta_T)\). |
| N13.06 | [0.21,0.75,0.86,0.81] | NODE: moreover, if \(\eta_t=\eta\) for all \(t=1,\ldots,T\), then for every \(u\in V\), \(\operatorname{Reg}_T(u)\le R^2/(2\eta)+\eta S/2-\|x_{T+1}-u\|_2^2/(2\eta)\). |
| N13.07 | bottom [0.21,0.82,0.86,0.85] | NODE: proof instruction to divide Lemma 2.12 by \(\eta_t\) and sum over \(t=1,\ldots,T\), continued on p.14. |
| N13.08 | Algorithm 2.1 references | NODE / BOUNDARY_SOURCE_LEAF: Algorithm 2.1 is the source algorithm referenced by the lemma and theorem. The recurrence and gradient definition needed here are visible in N13.01; its full earlier pseudocode is outside the packet. |

### Printed 14 / PDF 26: proof continuation and all observations

| ID | Region | Disposition and source content |
|---|---|---|
| N14.01 | first display line [0.21,0.17,0.86,0.22] | NODE: summed one-step inequality, \(\operatorname{Reg}_T(u)\le\sum_{t=1}^T[\|x_t-u\|_2^2/(2\eta_t)-\|x_{t+1}-u\|_2^2/(2\eta_t)]+\sum_{t=1}^T\eta_t\|g_t\|_2^2/2\). |
| N14.02 | second line [0.24,0.22,0.86,0.26] | NODE: summation rearrangement gives initial/terminal terms plus \(\sum_{t=1}^{T-1}(1/\eta_{t+1}-1/\eta_t)\|x_{t+1}-u\|_2^2/2\), plus the gradient sum. |
| N14.03 | third line [0.24,0.26,0.86,0.30] | NODE: replace initial squared distance and weighted intermediate squared distances by \(D^2\). Source theorem's nonincreasing positive stepsizes make the reciprocal-difference coefficients nonnegative; domain membership/diameter supply the distance bounds. Terminal negative squared-distance term is retained. |
| N14.04 | last two lines [0.24,0.30,0.86,0.38] | NODE: reciprocal differences telescope to \(D^2/(2\eta_T)\), giving the first Theorem 2.13 bound with the full negative endpoint term. |
| N14.05 | constant-rate paragraph and display [0.21,0.39,0.86,0.49] | NODE: constant \(\eta_t=\eta\) case directly telescopes the unweighted squared distances, producing \(R^2/(2\eta)-\|x_{T+1}-u\|_2^2/(2\eta)+\eta S/2\). This retains initial distance instead of diameter. |
| N14.06 | observation 1 [0.21,0.53,0.86,0.58] | NODE / WARNING: squared-gradient terms reflect producing \(x_t\) before knowing \(\ell_t\); source says they become nonpositive if the loss is observed first; cites Section 15.5.1. The latter claim is not established in this packet. |
| N14.07 | observation 2 [0.21,0.58,0.86,0.62] | NODE / BOUNDARY: constant-rate bound holds even if \(D=\infty\); its initial term depends on distance from \(x_1\) to the competitor \(u\). |
| N14.08 | observation 3 [0.21,0.62,0.86,0.65] | NODE: last term in both bounds is nonpositive and usually discarded; source explicitly warns that some advanced proofs need it. This is the stated justification for the p.15 relaxed expression. |
| N14.09 | observation 4 [0.21,0.65,0.86,0.74] | NODE / WARNING: time-varying rates require control of \(\|x_t-u\|_2^2\); source uses bounded \(V\), notes this fails in many ML applications, cites Section 5.2 for OGD failure on unbounded domains with time-varying rates, and Chapter 3 for the different stochastic SGD situation. These cited claims remain unproved leaves here. |
| N14.10 | observation 5 [0.21,0.74,0.86,0.79] | NODE / MOTIVATION: regret analysis guides the choice of \(\eta_t\); retain the author's justification requirement as prose, not an additional mathematical premise. |
| N14.11 | final paragraph [0.21,0.80,0.86,0.85] | NODE: choose a constant learning rate minimizing the bounds for a fixed number of iterations; sentence continues onto p.15. |
| N14.C1 | references in N14.06/N14.09 | NODE / BOUNDARY_SOURCE_LEAF: Section 15.5.1, Section 5.2, Chapter 3. Their assertions are preserved as cited warnings, not imported as proved prerequisites of the scalar calculation. |

### Printed 15 / PDF 27: entire target page

| ID | Region | Disposition and source content |
|---|---|---|
| N15.01 | opening paragraph/display [0.21,0.15,0.86,0.21] | NODE: minimize \(R^2/(2\eta)+\eta S/2\) with respect to \(\eta\). The source does not print a separate feasible-set subscript here. Positive learning rates are inherited from the preceding analysis. |
| N15.02 | following sentence [0.21,0.22,0.86,0.25] | NODE: source asserts the optimal \(\eta=R/\sqrt S\). It supplies no derivative, square-completion, or AM–GM derivation. |
| N15.03 | displayed result [0.40,0.27,0.64,0.32] | NODE: source says this would give regret bound \(R\sqrt S\). |
| N15.04 | warning paragraph [0.21,0.33,0.86,0.40] | NODE / WARNING: using that stepsize requires all future gradients, which depend on \(\eta\) itself, and the distance between the optimal solution and the initial point. An adversary can observe the chosen learning rates and select losses so that the chosen rate is no longer the correct one. Preserve both future-information and endogenous-gradient warnings. |
| N15.05 | next paragraph, first half [0.21,0.41,0.86,0.45] | NODE / BOUNDARY: source calls this kind of rate impossible, citing a Chapter 5 lower bound, and says similar rates are possible with adaptive Section 4.2 and parameter-free Chapter 13 algorithms. Exact lower-bound quantifiers and alternative algorithm guarantees are outside this packet. |
| N15.06 | paragraph second half [0.21,0.45,0.86,0.50] | NODE / CONDITIONS: minimize a loose upper bound; assume gradient norms bounded by \(L\), explicitly \(\|g_t\|_2\le L\); assume bounded diameter and upper-bound \(R\) by \(D\). Implicit range is every round \(t=1,\ldots,T\), with the same \(L\). |
| N15.07 | minimization display [0.38,0.51,0.70,0.54] | NODE: literal \(\eta^\star=\operatorname*{argmin}_{\eta}\{D^2/(2\eta)+\eta L^2T/2\}=D/(L\sqrt T)\). The source writes a scalar `argmin` and no explicit positivity assumptions on \(D,L\) in this display. |
| N15.08 | next prose/display [0.21,0.55,0.86,0.59] | NODE: resulting regret bound \(DL\sqrt T\), numbered (2.1). |
| N15.09 | subsequent paragraph [0.21,0.60,0.86,0.63] | NODE / ASYMPTOTIC BOUNDARY: source calls regret sublinear in time and promises Chapter 5 optimality up to constant multiplicative factors. The latter is an external source leaf, not proved on this page. |
| N15.C1 | citations N15.05/N15.09 | NODE / BOUNDARY_SOURCE_LEAF: Chapter 5 lower bound/optimality, Section 4.2 adaptive algorithms, Chapter 13 parameter-free algorithms. These are context, not an AND requirement for the scalar inequality. |
| X15.10 | Example 2.14 [0.21,0.65,0.86,0.76] | EXCLUDED: application to the first chapter's guessing game, derivative \(2(x-y_t)\) on \([0,1]\), clipping projection, \(O(\sqrt T)\) rate and Chapter 4 improvement. Not a premise or proof of the selected minimization. Kept in raw image/text for coverage and reader context. |
| N15.11 | Example 2.15 opening [0.21,0.77,0.86,0.85] | NODE / BOUNDARY EXAMPLE: linear prediction \(\langle z_t,x_t\rangle\), \(z_t\in\mathbb R^d\), \(V=\mathbb R^d\), Huber loss after observing \(y_t\). Included because the continuation shows that constant-rate reasoning need not assume bounded diameter. Not a proof dependency of N15.07. |

### Printed 16 / PDF 28: boundary example and excluded next section

| ID | Region | Disposition and source content |
|---|---|---|
| N16.01 | Huber display [0.21,0.15,0.86,0.21] | NODE / BOUNDARY EXAMPLE: writing \(r=\langle z_t,x\rangle-y_t\) only as shorthand, source loss is \(r^2/2\) if \(|r|\le\delta\), else \(\delta(|r|-\delta/2)\). |
| N16.02 | paragraph after display [0.21,0.22,0.86,0.26] | NODE / BOUNDARY EXAMPLE: \(\delta\) is the outlier threshold; use a constant learning rate \(\eta\propto1/\sqrt T\). The coefficient of proportionality is not specified on this page. |
| N16.03 | gradient display [0.21,0.27,0.86,0.31] | NODE / BOUNDARY EXAMPLE: gradient is \(rz_t\) if \(|r|\le\delta\), else \(\delta\operatorname{sign}(r)z_t\). |
| N16.04 | final example paragraph [0.21,0.31,0.86,0.36] | NODE / BOUNDARY EXAMPLE: assume all \(\|z_t\|_2\) bounded, hence gradients bounded; cites Theorem 2.13 and says average performance approaches that of any fixed linear predictor. This uses fixed-comparator/initial-distance reasoning, not a finite diameter for \(\mathbb R^d\). |
| X16.05 | Section 2.2 heading/paragraph [0.21,0.39,0.86,0.50] | EXCLUDED: nonsmooth convex losses, absolute/hinge-loss examples and replacing gradients by subgradients begin a new section, outside the differentiable-loss minimization target. |
| X16.06 | Section 2.2.1 introduction [0.21,0.53,0.86,0.56] | EXCLUDED: transition to definitions for the next section. |
| X16.07 | Definition 2.16 [0.21,0.57,0.86,0.61] | EXCLUDED: closed extended-real function definition, not a prerequisite of the selected scalar calculations. |
| X16.08 | next paragraph/citation [0.21,0.61,0.86,0.65] | EXCLUDED: equivalence with lower semicontinuity and Bauschke–Combettes Lemma 1.24 citation serve the next section. |
| X16.09 | Example 2.17 [0.21,0.65,0.86,0.67] | EXCLUDED: closed indicator-function example belongs to next section. |
| X16.10 | Definition 2.18 [0.21,0.67,0.86,0.70] | EXCLUDED: proper function definition belongs to next section. |
| X16.11 | following paragraph [0.21,0.70,0.86,0.74] | EXCLUDED: interest in convex proper functions belongs to next section. |
| X16.12 | Example 2.19 [0.21,0.74,0.86,0.76] | EXCLUDED: proper indicator-function example belongs to next section. |
| X16.13 | subgradient transition [0.21,0.77,0.86,0.79] | EXCLUDED: introductory sentence for Definition 2.20. |
| X16.14 | Definition 2.20/display [0.21,0.79,0.86,0.85] | EXCLUDED: subgradient definition and its universal \(y\in\mathbb R^d\) inequality belong to the next section, not this gradient stepsize target. |

## Proposed source proof topology

Edges run from input to consumer. All nodes are proposed; BOUNDARY_SOURCE_LEAF and SOURCE_GAP nodes are not discharged by this extraction. A warning/context edge is not a logical proof prerequisite.

| Consumer | Inputs / logic | Consumer use-site and premise discharge |
|---|---|---|
| N13.02 | N13.01 AND N13.03 AND N13.04 | Lemma 2.12, p.13. Closed convex projection and convexity are invoked by citation; \(\eta_t>0\), comparator membership and update are explicit. Full earlier facts are boundary leaves. |
| N14.01 | N13.02 AND N13.07 | p.13 last line to p.14 first line. Divide by positive \(\eta_t\), then sum over exactly \(1,\ldots,T\). |
| N14.02 | N14.01 | p.14 second displayed line: index rearrangement, keeping terminal \(T+1\). |
| N14.03 | N14.02 AND N13.05 | p.14 third line: positive nonincreasing rates imply nonnegative reciprocal differences; feasible iterates and comparator permit diameter bounds. No bound replaces the negative terminal term. |
| N14.04 | N14.03 | p.14 fourth/fifth lines: reciprocal-difference telescope. |
| N14.05 | N14.01 AND constant-rate condition in N13.06 | p.14 second display: direct constant-rate telescope. Finite diameter is unnecessary, as N14.07 says. This does NOT depend on the diameter replacement N14.03. |
| N15.01 | N14.05 AND N14.08 AND N14.11 | p.14 final paragraph and p.15 first display: discard nonpositive endpoint term and select the fixed-horizon positive-stepsize scalar expression. |
| N15.02 | N15.01 AND G15.01 | p.15 assertion 'optimal': source omits minimization derivation and domain/boundary qualification. |
| N15.03 | N15.02 AND G15.02 | p.15 result display: source omits explicit substitution into the bound. This is a conditional/hindsight calculation, constrained by N15.04. |
| N15.07 | N15.01 AND N15.06 AND G15.03 AND G15.04 | p.15 loose-bound paragraph/display: distance and per-round norm bounds lead to new coefficients; source omits the displayed bridge and minimization proof/domain qualifications. |
| N15.08 | N15.07 AND G15.05 | p.15 Eq. (2.1): substitute chosen rate into the loose bound. |
| N15.09 sublinear clause | N15.08 AND G15.06 | p.15 prose after (2.1): asymptotic conclusion requires interpretation of coefficient dependence as horizon grows. |
| N15.04/N15.05 | context edges from N15.02/N15.03 | These constrain algorithmic interpretation; they do not establish the scalar minimizer. Chapter 5 lower-bound claim remains a separate source leaf. |
| N16.04 | N15.11 AND N16.01 AND N16.02 AND N16.03 AND Theorem 2.13 constant-rate clause | p.16 example only. The full asymptotic application is not a second proof of the p.15 minimization. |

### Source gaps that must remain visible

| ID | Kind and exact use-site | Missing source detail |
|---|---|---|
| G15.01 | SOURCE_GAP at N15.02 | No proof of scalar optimality; no explicit \(R>0,S>0\) qualification; no treatment of zero coefficients; no explicit frozen-coefficient domain for the minimization. |
| G15.02 | SOURCE_GAP at N15.03 | Substitution/attainment bridge and its nondegenerate-domain qualification are asserted, not displayed. It cannot erase the endogenous-gradient warning. |
| G15.03 | SOURCE_GAP at N15.07, coefficient relaxation | The paragraph gives \(R\le D\) and \(\|g_t\|\le L\), but does not display \(S\le TL^2\) and the resulting scalar upper-bound inequality. Positivity of \(\eta\) is needed to preserve directions. |
| G15.04 | SOURCE_GAP at N15.07, argmin | No derivation or explicit feasible domain for scalar argmin; no printed nonzero \(D,L,T\) restrictions or degenerate regime discussion. |
| G15.05 | SOURCE_GAP at N15.08 | Substitution giving exactly \(DL\sqrt T\) is asserted without displayed algebra. |
| G15.06 | SOURCE_GAP at N15.09 | The sentence does not spell out that \(D,L\) must have suitable horizon-independent control for the sublinear-in-\(T\) reading. |
| G13.01 | SOURCE_GAP / inherited-domain clarification | Theorem 2.13 prints the monotonicity condition for \(t=1,\ldots,T-1\); at \(T=1\) that condition alone is vacuous. Positivity of the actual learning rate is inherited from Lemma 2.12/algorithmic convention and division, and should be made explicit in any precise extracted scalar contract. This is a flag for review, not a source-invalidity verdict. |

### OR-routes and separation from new mathematics

The selected printed p.15 argument gives a single asserted scalar minimization route, with G15.01/G15.04 left as gaps. The source does not provide both a calculus proof and an AM–GM proof. This packet therefore does not invent either as a source route or turn them into mandatory AND inputs.

There are two sufficient ways, using bounds already present on pp.13–15, to reach the diameter-based loose scalar bound:

1. **Printed p.15 route:** `(N15.01 AND R≤D AND each ||g_t||≤L AND G15.03)`.
2. **Alternative source-supported composition, proposed rather than printed p.15 derivation:** `(N14.04 AND eta_t=eta>0 AND each ||g_t||≤L AND endpoint-discard N14.08 AND corresponding relaxation bridge)`.

If the reviewer elects to include both routes to that same loose scalar-bound node, their combination is **route 1 OR route 2**, never an AND of the distance and diameter proofs. Route 2 is an extraction proposal from source ingredients, not an attributed additional proof paragraph. Its finite-diameter assumptions do not propagate backward into the constant-rate initial-distance bound. The separate hindsight and diameter minimizations have different coefficients and information semantics and are not interchangeable OR proofs of the same online implementability claim.

## Literal claims versus mathematical qualifications

The following are extraction-time qualifications for independent review. They are not words silently inserted into the pinned source, not newly proved results, and not approved repairs.

| Issue | Literal source | Qualification / review obligation |
|---|---|---|
| Scalar variable | minimize with respect to \(\eta\), positive learning-rate context | Domain should be stated as real \(\eta>0\). An unrestricted real argmin is not the printed OGD context. |
| Fixed coefficients | first expression uses realized \(g_t\); warning says they depend on \(\eta\) | A scalar identity in fixed numbers \(R,S\) is not an optimization theorem for the full map \(\eta\mapsto g_t(\eta)\), nor a feasible online rule. The source itself warns against this interpretation. |
| Comparator quantifiers | Theorem 2.13: all \(u\in V\); warning mentions distance to 'optimal solution' | Keep regret comparator-specific. No existence of a loss minimizer is established here. For each comparator a hindsight expression can differ; one \(\eta\) is not asserted to attain every comparator's scalar optimum simultaneously. |
| First formula interior regime | \(R/\sqrt S\) without cases | For an attained positive finite candidate the natural interior regime is \(R>0,S>0\). With \(R=0,S>0\), the candidate is zero, outside domain; with \(R>0,S=0\), denominator vanishes; with both zero the formula is \(0/0\). Distinguish minimum from infimum, and do not encode a default quotient as source semantics. |
| First formula boundary candidates | no boundary discussion | Candidate boundary classification to verify separately: \(R=0,S>0\) has infimum 0 approached as \(\eta\downarrow0\); \(R>0,S=0\) has infimum 0 as \(\eta\to\infty\); \(R=S=0\) gives value 0 at every positive \(\eta\). No such infimum assertion is literally printed. |
| Loose formula interior regime | \(D/(L\sqrt T)\) and \(DL\sqrt T\) | Natural nondegenerate regime: finite \(D>0,L>0\), positive integer horizon \(T\). Zero diameter, zero gradient bound or empty horizon need their own treatment. D is a domain diameter, not automatically a positive constant. |
| Loose boundary candidates | no cases | Candidate classification for review: if \(D=0,L^2T>0\), the scalar infimum is approached at zero; if \(D>0,L^2T=0\), at infinity; if both coefficients vanish every positive rate minimizes. \(T=0\) lies outside the inherited \(\eta_T\)/iteration notation and is not covered by the printed formula. |
| Coefficient dependence | common \(L\), bounded diameter \(D\), fixed iteration count | A usable advance choice requires valid known bounds before the relevant play and the horizon needed for this fixed-horizon schedule. The source gives no unknown-horizon tuning theorem here. Uniform sublinear asymptotics cannot be inferred if coefficients grow arbitrarily with \(T\). |
| Gradient bound quantification | \(\|g_t\|_2\le L\) | Per-round bound for the actual run is the literal premise. A bound uniform over candidate runs/losses is a stronger specification that may justify pre-tuning, but is not explicitly quantified in the display. It must not be silently substituted for the literal premise. |
| Unbounded domains | constant-rate bound holds with \(D=\infty\) | Retain the comparator-dependent \(R\) bound. Finite \(D\) is a condition of the later diameter tuning, not of all constant-rate regret bounds. |
| Endpoint | negative term is usually discarded | The p.15 scalar objective is a relaxed upper bound. Its scalar minimizer need not minimize the full bound retaining \(x_{T+1}\), or actual regret. |
| Probability/feedback | deterministic sequence guarantee; play before seeing loss; adversarial warning | Do not convert this to an expectation, high-probability event, stochastic-rate theorem, or bandit feedback guarantee. No filtration is specified in this passage. |
| Example 2.15 | \(\eta\propto1/\sqrt T\), bounded features, any fixed linear predictor | This is separate initial-distance asymptotic context. It does not supply finite diameter for \(\mathbb R^d\), uniformity over all comparator distances, or a specified optimal proportionality coefficient. The threshold's positivity is conventional but not explicitly printed in the shown paragraph. |

## Separate proposed repair/specification layer

These are proposals only. The pinned formulas/text above are unchanged. Independent source/repair review is required before any statement is called faithful or corrected.

- P1: State a frozen-coefficient scalar minimization contract over \(\eta>0\), with \(R>0,S>0\), and a separate domain-complete boundary/infimum contract if desired. Keep the OGD application and its endogenous-gradient warning separate.
- P2: State the diameter-tuned application with explicit finite positive \(D,L\), positive finite horizon, valid per-round gradient bounds, and the inherited OGD assumptions. Clarify what advance knowledge is required. Do not label a stronger uniform-in-\(\eta\) bound as literally printed unless separately identified.
- P3: Treat zero-coefficient regimes separately rather than using totalized division or silently deleting them from a source-faithfulness claim. No repair approval is recorded here.
- P4: Preserve the original fixed-comparator constant-rate guarantee on unbounded domains and the negative endpoint term in the source contract; show discarding it only at the relaxed-objective step.

## Review handoff

The independent reviewer should first inspect the raw page PNGs/text, then this proposed inventory/topology, without implementation Lean or private extractor reasoning. Check source coverage, edge direction, missing domain cases, coefficient dependence, all-\(u\) versus comparator-dependent tuning, conditional premises, OR structure, the gap labels, and the exact distinction between a scalar minimization identity and an online algorithm guarantee. The extracted gaps and proposals are not reviewer verdicts. Whole-book/source-root closure remains outside this bounded packet.
