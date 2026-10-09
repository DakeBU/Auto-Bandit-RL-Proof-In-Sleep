# Conversion Window: Source losses and unique prescient updates

Task id: `ONLINE-CH2-PRESCIENT-SOURCE-20261010`
Source card: `docs/contracts/online-ch2-prescient-source-v1/source-card-v1.json`
Scenario: prescient current whole-loss feedback before the paid action; deterministic, no probabilistic semantics.

## Natural-Language Statement

Orabona v10 Algorithm15.8 and Theorem15.30, printed265-266/PDF277-278, required Chapter2 forward dependency. A valid source argmin run is identified with the existing partial canonical recursion using uniqueness, then receives the printed fixed and variable bounds. It is not a claim of universal argmin attainment. Exact draft headers and binder contexts are in headers-draft-v2.json. Finite-dimensional source endpoints infer completeness; helper scopes are separately listed.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| loss_t | current extended-real loss with no minus infinity | loss t : E -> EReal | source t=1..T maps to Lean t=0..T-1 | draft |
| x_t | paid current minimizer | x (t+1) | base is x t, initial x0 | draft |
| B_psi(a;b) | target first, interior base second | OnlineBregman.divergence psi a b | ambient representative restricted to X | existing |
| argmin | actual attained extended-real minimum | IsMinOn plus feasible point | not a regret/stability premise | draft |
| psi closed on X | closed extended-real restriction | SourceClosed (coe psi + extendedIndicator X) | canonical zero/top indicator | draft |

## Assumption Ledger

Source endpoints: real finite-dimensional inner-product space, V nonempty/closed/convex subset X, real ambient representative psi strictly convex on X and differentiable on interior X, canonical restricted generator closed, x0 in interior X, all supplied updated states in interior X, positive played steps, global no-bottom losses and V subset effective domain, global supporting subgradients at all feasible points. Variable endpoint requires T>0 and nonincrease only between played steps. Fixed endpoint allows T=0. Given actual attained minima are the algorithm's run hypothesis. No bounded V, future feedback input, global convexity of total toReal, source regularizer value outside X, or source attainment from closedness/strictness is assumed.

The strict objective helper has no interior/differentiability/closedness premise: its total derivative is linear, so this is algebraic strict convexity only. Source endpoints license the intended Bregman semantics at their interior bases. The initial state need not lie in V or a loss domain. Comparator lies in V. T=0 fixed loss sum is empty; variable finite maximum is never taken over an empty set.

## Local API And Proof Route

Reuse canonical divergence/advance/iterate and actual-minimum bridge. First prove the properness producer, then strict objective, uniqueness, recursive identification, and source endpoint transports. Readiness is the DAG below; one lower route. No external dependency/toolchain change. No theorem bodies before distinct contract review and stabilization.

## Proof-DAG

See `docs/contracts/online-ch2-prescient-source-v1/dependency-DAG-draft-v1.json`. SourceProper producer has two real endpoint consumers. No extra shared clone, no per-Book library. Global SGB frontier and registry remain unchanged during draft/proving.

## Gaps

All six terminals remain open before proving. Full chapter and eight required forward containers remain open. The historical unconditional-choiceability wording versus source conditional valid-run guarantee needs a separate source audit/classification, not silent deletion. Closedness assumptions remain in source wrappers even when the conditional argument does not use them. No universal attainment or new source erratum is claimed.
