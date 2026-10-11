# Prescient Euclidean source topology — proposal

Source-only map of PDF26,277,278, personally inspected from newly rendered pinned-PDF pixels. No new production/Test/BODY file was read. Distinct reviewer required; no selfacceptance.

Every scoped statement and displayed proof stage has a stable node below. Source hypotheses are separate from proof-dependency edges. The JSON records exact equations, AND/OR semantics, page hashes and explicit exclusions.

- `SRC-C2-PRESCIENT` [SOURCE_RESULT], PDF26: The gradient-square terms arise from output before seeing the loss; with current loss visible before output these terms become nonpositive; pointer15.5.1.
- `SRC-ORACLE` [SOURCE_INFORMATION_CONSTRAINT], PDF277: Looking at the loss before prediction changes the oracle: access to entire functions rather than only gradients. This leaf does not identify prescient access with ordinary OGD feedback.
- `SRC-MOTIVATION` [SOURCE_CONTEXT], PDF277: Best response only guarantees nonpositive regret; optimistic coupling needs specific negative terms, motivating Prescient OMD. Nonpositive total regret of best response is not the POMD bound.
- `SRC-ALG15.8` [SOURCE_ALGORITHM], PDF277: Receive ell_t; choose x_t in argmin over V of ell_t(x)+Bpsi(x;x_(t-1))/eta_t; pay ell_t(x_t).
- `SRC-TH15.30-VAR` [SOURCE_RESULT], PDF277: R_T(u)<=max_{0<=s<=T-1}Bpsi(u;x_s)/eta_T-sum_{t=1}^T Bpsi(x_t;x_(t-1))/eta_t.
- `SRC-TH15.30-FIX` [SOURCE_RESULT], PDF277: R_T(u)<=Bpsi(u;x_0)/eta-(1/eta)sum_{t=1}^T Bpsi(x_t;x_(t-1)).
- `SRC-OPTIMALITY` [SOURCE_PROOF_CLAIM], PDF277: Source cites Theorem2.8 to assert existence g_t in partial ell_t(x_t) with <eta_t*g_t+gradpsi(x_t)-gradpsi(x_(t-1)),u-x_t>>=0 for every u in V.
- `SRC-SUPPORT` [SOURCE_EQUATION], PDF277: eta_t*(ell_t(x_t)-ell_t(u))<=<eta_t*g_t,x_t-u>.
- `SRC-VARIATIONAL` [SOURCE_EQUATION], PDF277: <eta_t*g_t,x_t-u><=<gradpsi(x_(t-1))-gradpsi(x_t),x_t-u>.
- `SRC-THREEPOINT` [SOURCE_EQUATION], PDF277: <gradpsi(x_(t-1))-gradpsi(x_t),x_t-u>=Bpsi(u;x_(t-1))-Bpsi(u;x_t)-Bpsi(x_t;x_(t-1)); cited Lemma6.7.
- `SRC-ONES` [SOURCE_DERIVED_BOUND], PDF277: eta_t*delta_t<=Bpsi(u;x_(t-1))-Bpsi(u;x_t)-Bpsi(x_t;x_(t-1)).
- `SRC-SUM` [SOURCE_EQUATION], PDF278: R_T(u)<=sum_t(Bpsi(u;x_(t-1))/eta_t-Bpsi(u;x_t)/eta_t)-sum_t Bpsi(x_t;x_(t-1))/eta_t.
- `SRC-BYPARTS` [SOURCE_EQUATION], PDF278: Potential sum equals Bpsi(u;x_0)/eta_1-Bpsi(u;x_T)/eta_T+sum_{t=1}^{T-1}(1/eta_(t+1)-1/eta_t)*Bpsi(u;x_t). Movement sum remains subtracted.
- `SRC-DMAX` [SOURCE_DEFINITION], PDF278: D²=max_{0<=t<=T-1}Bpsi(u;x_t); previous-state maximum excludes x_T.
- `SRC-MAXBOUND` [SOURCE_EQUATION], PDF278: Replace initial/interior comparator divergences by D² using nonnegative reciprocal-step increments; drop -Bpsi(u;x_T)/eta_T using divergence nonnegativity. Bound becomes D²/eta_1+D² sum_{t=1}^{T-1}(1/eta_(t+1)-1/eta_t)-movement sum.
- `SRC-RECIPTELESCOPE` [SOURCE_EQUATION], PDF278: sum_{t=1}^{T-1}(1/eta_(t+1)-1/eta_t)=1/eta_T-1/eta_1.
- `SRC-VARFINISH` [SOURCE_EQUATION], PDF278: D²/eta_1+D²*(1/eta_T-1/eta_1)=D²/eta_T, retaining the full negative movement sum.
- `SRC-FIX-EXERCISE` [SOURCE_GAP], PDF278: Printed fixed-step proof is omitted by exercise instruction, but its theorem is mandatory. Reconstruct by constant-weight telescoping of SRC-SUM and drop only nonnegative terminal comparator divergence; keep every movement term.
- `SRC-NEGATIVE-INTERPRETATION` [SOURCE_RESULT], PDF278: The POMD regret bound contains the negative terms needed by optimistic algorithms; this does not imply its total regret is nonpositive.
- `SPEC-QUADRATIC` [SPECIALIZATION_BOUNDARY], PDF277: Set X=E and psi(z)=||z||²/2. Actual gradient at y is y and Bpsi(x;y)=||x-y||²/2. Shared geometry extends to complete real Hilbert spaces; consumers remain finite-dimensional.
- `SPEC-VAR` [SPECIALIZED_TARGET], PDF277: Actual Option run equality AND general EReal variable regret bound with previous-state half-squared-distance maximum divided by last played eta, minus sum of half movement squares divided by respective eta.
- `SPEC-FIX` [SPECIALIZED_TARGET], PDF277: Actual Option run equality AND initial squared-distance/(2eta) minus movement-square sum/(2eta); T=0 extension retained.

## Source route and specialization

The printed route is attained update → first-order variational inequality plus global loss support → three-point identity → one-step bound → sum → weighted telescoping → previous-state maximum and reciprocal telescoping → variable endpoint. The fixed endpoint has a SOURCE_GAP in the printed proof: its proof is left as an exercise but remains mandatory. Constant-weight telescoping supplies its intended mathematical reconstruction; this is not a claim of a new inspected Lean proof.

Quadratic geometry AND the variable endpoint yield the variable specialization; quadratic geometry AND the fixed endpoint yield the fixed specialization. Both are required. The prescient oracle receives the whole current loss before choosing and paying the new state. Initial feasibility is not added; X=univ gives interior automatically. Exact half factors, negative movements, previous-state max and last used step remain. The shared geometry allows complete Hilbert space; regret consumers retain finite-dimensional E. Actual attained-update premises give conditional valid-run statements; no global existence theorem is silently inferred.

The intended reuse of accepted source bounds is a prospective implementation route, not a discovered proof-value graph. The source first-order argument and the proximal-comparison approach are alternative proof strategies; do not claim any cited theorem is necessary. BTRL is another broader conceptual route, not permission to omit either frozen OMD endpoint.

## Explicit exclusions

- `EX-P26-OGD-DISPLAYS`: PDF26 upper variable/fixed OGD proof displays. Ordinary OGD upper-bound/telescoping results belong to separate C2 targets; contextual contrast only, not prescient proof obligations.
- `EX-P26-OTHER-BULLETS`: PDF26 bullets2–5 and bottom tuning paragraph. Constant-step unbounded domain, negative terminal, variable OGD failure/SGD and tuning are separately owned C2 mathematics; retained elsewhere, not discharged here.
- `EX-GAME-EQUILIBRIUM`: PDF277 introductory no-communication/saddle-point discussion and Remark15.16 pointer. Broader game-theoretic composition and oracle comparison are context; current whole-loss access captured by SRC-ORACLE, no saddle convergence claimed.
- `EX-ALG15.9`: PDF278 Algorithm15.9 and subsequent BTRL/BTL prose. Different cumulative algorithm, optional alternate route for primaryC2 implication but separately required in owningChapter15. Not the frozen Euclidean Algorithm15.8 leaf.
- `EX-TH15.31`: PDF278 last theorem opening continuingPDF279; Theorem7.47 citation. B4 terminal7.47/15.31 corrections remain required/open. Their omission from this leaf is explicit scope separation, not deletion or acceptance.

The scope includes every substantive leaf-relevant proof paragraph, including the final negative-term interpretation; total regret is not asserted nonpositive. PDF278 starts Theorem15.31 but its continuation and B4 repair are separately owned and open. No metadata/status/count change, no build and no wholeChapter15 completion. Requested GPT-6 Astra/medium is metadata, not runtime attestation.
