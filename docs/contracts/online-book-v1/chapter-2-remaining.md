# Chapter 2 remaining source obligations, v1 audit

Source v10 printed pp. 8-23, PDF pp. 20-35. The fixed and decreasing-step OGD packages are accepted locally; the remaining convex-analysis, subgradient, example and linearization statements below are still under contract review. No remaining statement is silently represented by the real-valued OGD specialization. All numbered required entries are in source-inventory.json. Formal results with exercise proofs remain required.

## Decreasing-step terminal reviewed intent

Algorithm 2.1: same nonempty closed convex V, initial x0 in V, actual recursion x(t+1)=project V (x(t)-eta(t)*gradient(loss(t),x(t))). Positive finite schedule; eta(t+1)<=eta(t) for t+1<T. T>=1. For each comparator u in V:

sum(t<T)(loss(t,x(t))-loss(t,u)) <= D^2/(2*eta(T-1)) + sum(t<T)(eta(t)/2*norm(gradient(loss(t),x(t)))^2) - norm(x(T)-u)^2/(2*eta(T-1)).

Source defines D as diameter. A bound D with all pairwise distances <=D is sufficient, but must be labelled as the upper-bound interface; the exact finite diameter corollary must instantiate it. Empty horizon is a separate zero-sum lemma, never fake eta(-1). Feasibility and prefix causality must be proved for the actual variable-step recurrence. DAG: inherited projection/first-order/one-step interfaces -> recurrence feasibility -> weighted telescoping identity -> monotone reciprocal coefficient estimate -> terminal. Do not assume one-step regret as an input to the public algorithm theorem.

## Convex analysis obligations

2.4: extended-real epigraph convexity equivalence on convex effective domain, excluding minus infinity. 2.5-2.6: affine functions and norms; all four printed closure operations required. 2.7: supporting gradient inequality for all y, including outside effective domain; inherited real-valued first_order is only a specialization. 2.8: constrained minimizer iff variational gradient condition, plus interior zero-gradient consequence. 2.9: measurable extended-real Jensen with integrable vector input; integrability/expectation conventions require careful audit, not a hidden stronger finite-loss assumption.

2.16/18/20/29 definitions: closed/lower-semicontinuous, proper, subdifferential, Lipschitz on domain. Indicator closedness/properness examples 2.17/19 included. Interior subgradient existence and absence outside domain included. 2.21: everywhere subdifferentiability on convex V implies convex restriction. 2.22: differentiability iff singleton subdifferential at a finite point; boundary and extended-real differentiability semantics must be reviewed explicitly. 2.23: sum inclusion AND equality under closed convex qualification (domain last function intersects all other interior domains). 2.24/25: abs subdifferential, indicator normal cone, interior zero cone and sphere normal rays. 2.26: finite maximum subdifferential equals convex hull of active subdifferentials, continuity at common finite point; index family nonempty must be explicit. 2.27 hinge example included. 2.28: affine pullback inclusion with adjoint. 2.30: Lipschitz iff bounded subgradient norm on interior domain; domain degeneracies retained.

## Algorithms and examples

2.10: actual FTL alternating linear-loss failure, regret >=T-3/2. 2.14: squared guessing gradient, interval projection formula, OGD guarantee. 2.15: Huber linear prediction, gradient formula, bounded-feature regret. 2.31 and Algorithm 2.2: actual subgradient feedback recursion, both one-step inequalities, inherited fixed/decreasing cumulative residual branches and tuning. The chosen subgradient depends only on current loss and current iterate; existence is not arbitrary full-sequence algorithm access. 2.32: absolute-loss guessing bound. Section 2.3: causal linearization and regret comparison. Unit-scaling example is an algebraic identity, not a separate regret theorem.

Progress: Chapter1 and the Theorem2.13 variable-step package passed local gates. Next: finish precise contracts for the remaining Chapter2 obligations after resolving the above domain semantics. No purported frozen Lean targets for unaudited extended-real results. No exclusions based on proof difficulty.

Extended-real convexity update: Definition2.2/2.3, Theorem2.4 and domain/indicator consequences passed the scoped local gates in runs/online-convex-20260914. Affine/norm examples and all four closure operations remain required. The unrestricted EReal-add interpretation has a mixed-infinity counterexample recorded in next-source-audit.md; resolve that source convention explicitly rather than silently assuming noBot. Chapter2 remains partial.

Examples2.5/2.6 update: exact affine/norm epigraph endpoints and their finite embedding iff passed all scoped local gates in runs/online-convex-examples-20260914. The four general closure operations remain required; next-closure-audit.md records primary-source support for explicitly distinguishing convex upper addition from ordinary mathlib EReal addition. This does not complete Chapter2.

Closure update: affine precomposition, arbitrary indexed supremum and monotone real convex composition passed all scoped gates in runs/online-convex-closures-20260914. The nonnegative linear-combination bullet remains required and awaits explicit upper-addition proof. No Chapter2 completion.

Fourth closure update: nonnegative combinations passed all local gates with explicit convex-analysis upperAdd and zero-weight semantics. Evidence runs/online-convex-sums-20260914 includes a compiled ordinary-addition counterexample. All four closure bullets are locally closed under this recorded interpretation; Theorems2.7-2.9 and all later required Chapter2 obligations remain incomplete.

Theorem2.7 update: full extended-real supporting-gradient endpoint passed all scoped local gates in runs/online-first-order-20260914, including an actual neighborhood-agreement proof and outside-domain canary. Theorem2.8, Theorem2.9 and later Chapter2 obligations remain required. No Chapter2 completion.

Theorem2.8 and its interior-zero consequence passed all scoped local gates in runs/online-optimality-20260914. Source neighborhood convexity is explicitly restricted to V, a documented strengthening with a public source-premise canary. No closed/bounded V assumed. Theorem2.9 Jensen and later required results remain incomplete.

Jensen update: full Theorem2.9 and geometric dependencies frozen in online-jensen-v2; all four targets remain unproved. Seven signed-expectation prerequisites passed local gates in runs/online-jensen-20260914/expectation-acceptance-decision.md. This is reusable foundation growth, not Jensen or Chapter2 completion. No loss-integrability, continuity or closed-domain premise added.
