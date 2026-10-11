# Source topology proposal v2 — T1/T2 successor

Proposal only, requiring distinct review. All22 original nodes and5 exclusions remain with unchanged claim texts and stable IDs; one new obligation node is added. Frozen headers and all prior artifacts remain untouched. No new production core, Test, BODY or snapshot was inspected.

## T1: literal source justification remains unresolved

SRC-OPTIMALITY preserves the author’s global-support existence claim and its Theorem2.8 citation, but explicitly records an unresolved SOURCE_GAP in proof justification/applicability. This is not a finding of source falsity. One and the SAME g_t must feed SRC-SUPPORT and SRC-VARIATIONAL; their combined one-step route cannot use two unrelated supports. The new optimality-to-support edge makes that binding explicit. Literal-route downstream edges carry the unresolved qualification.

The alternative proximal/segment route is separate: it can aim to establish the regret comparison without extracting that support, but does not prove or silently repair the author’s existence-of-g argument. Source topology is not implementation VALUE topology.

## T2: full frozen conjunction requires actual-run identification

New SPEC-ACTUAL-RUN records quadratic objective equality, strict-convex uniqueness/identification of feasible attained minima and finite induction from hinit to canonical Option equality. SRC-ALG15.8 AND SPEC-QUADRATIC feed this obligation with explicit H-ATTAINED, initialization, loss and ambient hypotheses. It is a mandatory AND parent of BOTH SPEC-VAR and SPEC-FIX, in addition to geometry and the respective regret endpoint. No proof is asserted, no total selector or universal attainment is inferred.

Variable target explicitly inherits positive/nonincreasing used steps, all source loss/feasible comparator interfaces, initialization, finite-dimensional quadratic context and H-NONEMPTY-HORIZON. Fixed target inherits the corresponding constant-positive-step interfaces and H-FIXED-HORIZON allowingT0. X=univ quadratic regularizer facts are derived obligations, not extra user assumptions. The source variable theorem now directly lists the nonempty-horizon condition needed by its finite maximum.

## Retained coverage

- `SRC-C2-PRESCIENT` (SOURCE_RESULT): The gradient-square terms arise from output before seeing the loss; with current loss visible before output these terms become nonpositive; pointer15.5.1.
- `SRC-ORACLE` (SOURCE_INFORMATION_CONSTRAINT): Looking at the loss before prediction changes the oracle: access to entire functions rather than only gradients. This leaf does not identify prescient access with ordinary OGD feedback.
- `SRC-MOTIVATION` (SOURCE_CONTEXT): Best response only guarantees nonpositive regret; optimistic coupling needs specific negative terms, motivating Prescient OMD. Nonpositive total regret of best response is not the POMD bound.
- `SRC-ALG15.8` (SOURCE_ALGORITHM): Receive ell_t; choose x_t in argmin over V of ell_t(x)+Bpsi(x;x_(t-1))/eta_t; pay ell_t(x_t).
- `SRC-TH15.30-VAR` (SOURCE_RESULT): R_T(u)<=max_{0<=s<=T-1}Bpsi(u;x_s)/eta_T-sum_{t=1}^T Bpsi(x_t;x_(t-1))/eta_t.
- `SRC-TH15.30-FIX` (SOURCE_RESULT): R_T(u)<=Bpsi(u;x_0)/eta-(1/eta)sum_{t=1}^T Bpsi(x_t;x_(t-1)).
- `SRC-OPTIMALITY` (SOURCE_PROOF_CLAIM): Source cites Theorem2.8 to assert existence g_t in partial ell_t(x_t) with <eta_t*g_t+gradpsi(x_t)-gradpsi(x_(t-1)),u-x_t>>=0 for every u in V.
- `SRC-SUPPORT` (SOURCE_EQUATION): eta_t*(ell_t(x_t)-ell_t(u))<=<eta_t*g_t,x_t-u>.
- `SRC-VARIATIONAL` (SOURCE_EQUATION): <eta_t*g_t,x_t-u><=<gradpsi(x_(t-1))-gradpsi(x_t),x_t-u>.
- `SRC-THREEPOINT` (SOURCE_EQUATION): <gradpsi(x_(t-1))-gradpsi(x_t),x_t-u>=Bpsi(u;x_(t-1))-Bpsi(u;x_t)-Bpsi(x_t;x_(t-1)); cited Lemma6.7.
- `SRC-ONES` (SOURCE_DERIVED_BOUND): eta_t*delta_t<=Bpsi(u;x_(t-1))-Bpsi(u;x_t)-Bpsi(x_t;x_(t-1)).
- `SRC-SUM` (SOURCE_EQUATION): R_T(u)<=sum_t(Bpsi(u;x_(t-1))/eta_t-Bpsi(u;x_t)/eta_t)-sum_t Bpsi(x_t;x_(t-1))/eta_t.
- `SRC-BYPARTS` (SOURCE_EQUATION): Potential sum equals Bpsi(u;x_0)/eta_1-Bpsi(u;x_T)/eta_T+sum_{t=1}^{T-1}(1/eta_(t+1)-1/eta_t)*Bpsi(u;x_t). Movement sum remains subtracted.
- `SRC-DMAX` (SOURCE_DEFINITION): D²=max_{0<=t<=T-1}Bpsi(u;x_t); previous-state maximum excludes x_T.
- `SRC-MAXBOUND` (SOURCE_EQUATION): Replace initial/interior comparator divergences by D² using nonnegative reciprocal-step increments; drop -Bpsi(u;x_T)/eta_T using divergence nonnegativity. Bound becomes D²/eta_1+D² sum_{t=1}^{T-1}(1/eta_(t+1)-1/eta_t)-movement sum.
- `SRC-RECIPTELESCOPE` (SOURCE_EQUATION): sum_{t=1}^{T-1}(1/eta_(t+1)-1/eta_t)=1/eta_T-1/eta_1.
- `SRC-VARFINISH` (SOURCE_EQUATION): D²/eta_1+D²*(1/eta_T-1/eta_1)=D²/eta_T, retaining the full negative movement sum.
- `SRC-FIX-EXERCISE` (SOURCE_GAP): Printed fixed-step proof is omitted by exercise instruction, but its theorem is mandatory. Reconstruct by constant-weight telescoping of SRC-SUM and drop only nonnegative terminal comparator divergence; keep every movement term.
- `SRC-NEGATIVE-INTERPRETATION` (SOURCE_RESULT): The POMD regret bound contains the negative terms needed by optimistic algorithms; this does not imply its total regret is nonpositive.
- `SPEC-QUADRATIC` (SPECIALIZATION_BOUNDARY): Set X=E and psi(z)=||z||²/2. Actual gradient at y is y and Bpsi(x;y)=||x-y||²/2. Shared geometry extends to complete real Hilbert spaces; consumers remain finite-dimensional.
- `SPEC-VAR` (SPECIALIZED_TARGET): Actual Option run equality AND general EReal variable regret bound with previous-state half-squared-distance maximum divided by last played eta, minus sum of half movement squares divided by respective eta.
- `SPEC-FIX` (SPECIALIZED_TARGET): Actual Option run equality AND initial squared-distance/(2eta) minus movement-square sum/(2eta); T=0 extension retained.
- `SPEC-ACTUAL-RUN` (SPECIALIZATION_ALGORITHM_INTERFACE_OBLIGATION): Identify the actual canonical Option run from the supplied attained quadratic updates: prove quadratic objective equality with the shared Bregman objective; use source loss support/convexity and positive-step quadratic strict convexity for uniqueness of feasible minima; identify the actual Classical.choose minimizer with x(t+1); induct from hinit to obtain iterate(t)=some(x(t)) for all t<=T.

All five exclusions remain unchanged: ordinaryOGD displays/otherC2 bullets, game-equilibrium context, BTRL15.9 and Theorem15.31/B4 are separately owned. Fixed-step SOURCE_GAP remains mandatory, not an omission. V1 pixel/text hashes are preserved with explicit repository-relative references. No chapter/source acceptance, denominator or status change. Requested Astra/medium; no runtime attestation.
