# Fresh statement-only decoding

## Exposure and provenance

Only the two assigned neutral input files were read. No source text, nearby metadata, earlier review, proof, or imported module was consulted. The decoder received the task instruction and inherited workspace/team instructions; thus source-unexposed means unexposed to the original mathematical source, not devoid of all project context. No source identity is inferred.

Input raw SHA-256 hashes, verified against the supplied expected values:

- `next-target-header-v1.txt`: `fd0cccb6f5deb86a63466516a49531db7599cb983620072782726e5ecc136efa`
- `next-target-header-v1-neutral-definitions.txt`: `707df92f3a1660b96427ee14949e10ff92d3095a064ebfcce143c6dd2bdcd2cd`

No specific model or reasoning effort was requested in the decoder assignment. Runtime model/effort is not attested here.

## Full natural-language statement

Let E be any nontrivial finite-dimensional real inner-product space with its given normed additive group structure. For every real exponent alpha strictly between zero and one, and for every natural-number horizon T satisfying

\[
T\geq \frac{2}{(1-\alpha)\phi(\alpha)},\qquad
\phi(\alpha)=\frac{1}{2-\alpha}+\frac{2^{-(1-\alpha)}-1}{1-\alpha},
\]

there exists a sequence of real-valued losses on E, indexed by all natural numbers, such that each loss at an index t<T is convex on all of E, globally 1-Lipschitz, and differentiable everywhere over the reals. Starting at zero and using the gradient update with step size (t+1)^(-alpha), the sum of the realized losses minus the losses of the fixed zero comparator over t=0,...,T-1 is at least one half phi(alpha) times T^(2-alpha).

Explicitly, writing f_t=loss t, the actual iterates and regret are

\[
x_0=0,\qquad \eta_t=(t+1)^{-\alpha},\qquad
x_{t+1}=x_t-\eta_t\nabla f_t(x_t),
\]
\[
R_T(0)=\sum_{t=0}^{T-1}\bigl(f_t(x_t)-f_t(0)\bigr),\qquad
R_T(0)\geq \frac12\phi(\alpha)T^{2-\alpha}.
\]

In the supplied definitions the update first projects onto the domain. The domain in this theorem is all of E, so this projection is the identity and the displayed unconstrained update is its mathematical interpretation. The regret is evaluated on these recursively generated gradient iterates, not on a separately postulated decision sequence.

## Seven statement slots

1. **Objects.** An arbitrary nontrivial finite-dimensional real inner-product space E; a scalar alpha; a natural horizon T; and an existential sequence f: N -> E -> R. The optimization domain is E itself. The step schedule, iterates, comparator, and regret are fixed by the supplied definitions.

2. **Quantifier order.** Universally quantify E and its stated structures, then alpha with 0<alpha and alpha<1, then T with the displayed threshold; only then choose the entire loss sequence f. The existential witness may depend on E, alpha, and T. The statement does not supply one sequence that works simultaneously for every eligible T. The regularity clause universally quantifies t<T after the loss sequence is chosen.

3. **Assumptions.** E has NormedAddCommGroup, InnerProductSpace over R, FiniteDimensional over R, and Nontrivial instances. Alpha lies strictly in (0,1). T satisfies the explicit real-valued threshold. Completeness needed by the projection definitions is available for a finite-dimensional real normed space and is not an additional independently imposed hypothesis in the theorem header. Convexity, Lipschitzness, and differentiability are guarantees of the existentially chosen losses, not supplied hypotheses on an externally fixed loss sequence.

4. **Conclusion.** There exists f with the regularity properties at every t<T, together with the lower bound on the actual gradient-descent regret R_T(0). Both the initial point and comparator are zero: the two consecutive zeros in regretVariable fill the x1 and u arguments. The result is against this fixed comparator; it is not a displayed equality with regret against a minimizing comparator. No upper regret bound is stated.

5. **Constants and time indexing.** Phi(alpha) is exactly the displayed scalar function. The Lipschitz constant is exactly 1 as an admissible bound, not a claim that the minimal Lipschitz constant equals 1. The lower-bound prefactor is exactly 1/2, and the exponent is 2-alpha. The threshold is exactly 2/((1-alpha)*phi(alpha)). Natural T is cast to R in this threshold and the power. Rounds are indexed from t=0; the first step size is 1 and the last step size used to form x_T is T^(-alpha). The argument named x1 in the definitions is the iterate at index 0, not index 1. The last regret summand uses x_(T-1), whereas the last loss can also define the subsequent x_T. Phi positivity is not a separate explicit premise or conclusion in this header.

6. **Feedback and algorithm.** On round t the loss is incurred at x_t; its gradient at that same point drives x_(t+1). The recurrence therefore specifies gradient feedback sufficient for this mathematical update. It does not encode a bandit observation model, stochastic oracle, noisy gradient, randomized choice, or an explicit information filtration. There is no need to choose among subgradients for the guaranteed differentiable losses. Whether the losses are presented by an adaptive adversary or fixed in advance is not formalized by the statement beyond existential choice of a complete sequence.

7. **Boundaries and opacity.** Only t<T losses are guaranteed convex, globally 1-Lipschitz and everywhere differentiable. The sequence is defined at all natural indices, but no analogous properties are asserted beyond the horizon. Differentiable means a real Frechet derivative exists at every point; it does not assert a continuous derivative, Lipschitz gradient, twice differentiability, or strong convexity. No formula for the chosen losses or their gradients appears, so their construction and the proof of their properties cannot be reconstructed from these files. The theorem is existential, not an exposed executable construction. Imported definitions of gradient and foundational projection-existence results are not expanded in the neutral files; their standard mathematical meanings suffice for this statement decoding, but their internal implementations were not inspected. No proof or source-fidelity verdict is provided.

## Comprehension status

No statement-level comprehension blocker remains: all task-specific definitions needed to identify the algorithm, schedule, domain, comparator, time range, constant, and regret are supplied. The loss construction and proof are intentionally absent, so this decoding cannot validate them. No builds or canonical edits were performed.
