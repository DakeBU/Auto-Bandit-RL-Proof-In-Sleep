# Independent source-header review: unbounded actual OGD

Verdict: **accepted-with-explicit-delta**, for the proposed header/source contract only. No blocking repairs. Actor `/root/adaptive_decoder`, distinct from formalizer `/root/adaptive_formalizer` and fresh decoder `/root/unbounded_header_blind`; prior source exposure disclosed. No runtime model attestation, new BODY, build, canonical edit or chapter closure.

Pinned Orabona v10 SHA256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; personally inspected PDF26/printed14 pointer and PDF64–65/printed52–53 theorem/proof, including existing pixels and actual PDF text. Chapter2 says OGD can fail; Theorem5.4 states unprojected OSD and proves it with differentiable linear losses. This distinction must remain explicit.

## objects — accepted-with-explicit-delta

Source proof explicitly treats d=1 then d>=2 by coordinate embedding; header uses Nontrivial finite-dimensional real inner-product E. This is coordinate-free Euclidean scope, not an infinite-dimensional claim. Nontrivial makes necessary d>=1 explicit; zero dimension cannot realize positive regret at0.

## quantifiers — accepted

For every alpha in(0,1) and every natural T meeting the threshold, choose a loss sequence; then regularity for every t<T. Source witness switches after ceil(T/2), so dependence on T is required/permitted. Nat-indexed extension beyond T is harmless and unconstrained. No single witness uniform in T or forall-loss lower bound.

## assumptions — accepted-with-explicit-delta

Exact strict alpha range and threshold are retained. Convexity, global 1-Lipschitzness and global differentiability are output witness properties, not input restrictions concealing the construction. Differentiability is extra relative to the printed theorem, justified by its explicit linear witness. Completeness is inferred from finite-dimensional real normed space, no new independently supplied premise.

## conclusion_metric — accepted

Exact lower bound on actual regretVariable(fullSpace,powerSteps,loss,0,0,T), the sum of played losses minus zero-comparator losses. This is not best-comparator infimum regret, expected regret, arbitrary trajectory regret, or all-algorithm minimax. Full-space projection is identity by inspected project_fullSpace; actual gradient trajectory transfer remains proof debt.

## constants_time — accepted

phi(alpha)=1/(2-alpha)+((1/2)^(1-alpha)-1)/(1-alpha), T>=2/((1-alpha)phi(alpha)), lower coefficient1/2 and exponent2-alpha exactly match PDF64. Source round1 maps to Lean0, eta(t)=(t+1)^(-alpha); first step1; regret last output indexT-1 and next stateT. Initial point and comparator both0. ceil(T/2)=(T+1)/2 in natural division matches existing switchSlope.

## feedback_causality — accepted-with-explicit-delta

C2PDF26 explicitly says OGD can fail; owning Theorem5.4 states unprojected OSD. Source proof uses losses -x then+x, with unique subgradient equal to gradient. Proposed actual OGD is valid source-target refinement only through explicit affine witness/gradient/iterate transport. Output precedes current loss and update. No stochastic oracle, adaptive filtration or selector-choice premise is hidden.

## boundaries — accepted-with-explicit-delta

Header extracts only failure endpoint. Printed phi range and limit1-log2>=0.3 remain separate source components, with existing phi_range/phi_limit reused, not discharged again by this header. Alpha endpoints excluded; T0 cannot satisfy positive threshold given existing phi positivity. No arbitrary varying schedule, bounded-domain failure, strong convexity, gradient Lipschitzness, or competing FTRL impossibility asserted.

## Required explicit producer route

- `OnlineUnboundedOSD.switchLoss / switchSlope`: lines17–19: slope=-1 for t<(T+1)/2, +1 otherwise; loss=slope*inner(v,z). Unit v produces linear finite real losses matching printed witness.
- `OnlineUnboundedOSD.switching_loss_regular`: lines126ff: convexity and LipschitzWith1 for every t when norm(v)=1; does NOT export differentiability.
- `OnlineGradientDescentSource.gradient_linear`: lines53ff: actual gradient of inner(g,z) equals g. Rewrite switchLoss as inner(switchSlope*T-index smul v,z); no T multiplicative factor.
- `OnlineGradientDescentSource.linear_regular / InnerProductSpace.toDual`: lines45–58: differentiability of continuous linear inner functional available. Global Differentiable for constructed witness must be explicitly produced, not inferred from arbitrary convex Lipschitz loss.
- `OnlineUnboundedOSD.currentSubgradient_affine / step_affine_fullSpace / iterate_affine_prefix`: lines32–80: unique affine subgradient and explicit same-run OSD prefix formula; supports local actual OGD=OSD trajectory equality under same witness and steps.
- `OnlineUnboundedOSD.switching_vector_lower_bound`: lines470ff: exact threshold/coefficient bound for explicit switchLoss T v, unit v, actual OSD regret. Appropriate producer to transport after proving actual OGD trajectory/regret equality.
- `OnlineUnboundedOSD.theorem_5_4`: lines516ff exports only existential convex/Lipschitz OSD losses. Opaque use cannot supply differentiability or actual OGD trajectory; alone insufficient.

Choose unit v using nontriviality; use the actual switchLoss T v. Prove its global differentiability and actual gradient, then identify OGD full-space iterates with the explicit affine OSD iterates, identify finite regret sums (including Real/EReal coercion semantics), and transport switching_vector_lower_bound. These are outstanding BODY obligations, not supplied premises or consequences of the opaque existential theorem.

## Review limits and clarification

- No blocking header/source mismatch found. No mathematical header correction requested.
- Metadata finite_witness phrase "switchSlope*T" should be read as switchSlope T t, not multiplication by T; actual definition and header are unambiguous. This wording clarification is nonblocking.
- Source pixels64/65 and26 personally inspected; original PDF raw hash independently verified. No missing-half or changed source constant alleged.
- Blind reconstruction a69315... matches all seven slots. Reviewer is source-exposed and distinct from formalizer and fresh blind actor; no claim of reviewer blindness.
- Header approval is not BODY authorization by this reviewer, elaboration, proof validation, package acceptance or chapter closure.

All eight forward containers and six future claims remain open; source proof denominator null and Goal ACTIVE. This endpoint does not re-prove or newly accept the separate phi range/limit claims.
