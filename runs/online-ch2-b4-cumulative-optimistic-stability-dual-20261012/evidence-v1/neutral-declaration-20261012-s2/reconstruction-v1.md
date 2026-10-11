# Header-only neutral reconstruction

## Scope and input identity

This reconstruction reads only `context-v1.txt` and `declaration-v1.txt` in this directory. No proof body, imported module, source paper, planning file, or contract was consulted. It describes the supplied header; it makes no proof-validity or source-acceptance claim.

- Context SHA256: `dda75233701f136a13d61c7d28e6b73dd2539d142f4504d2ff5f42468ea24f28`.
- Declaration SHA256: `6dd6994aca1486626223fe94d723a2cd951d8fa94e489627af9cd68b5e5e0cf5`.
- Qualified theorem name: `BanditRL.OnlineConvex.cumulative_optimistic_stability_dual_bound`.

## Binders in declaration order

1. Implicit `E : Type*`.
2. Typeclass `[NormedAddCommGroup E]`.
3. Typeclass `[NormedSpace ℝ E]`.
4. `V : Set E`.
5. `hV : Convex ℝ V`.
6. `psi : E → ℝ`.
7. `hint : E → ℝ`.
8. `loss : ℕ → E → EReal`.
9. `n : ℕ`.
10. `lam : ℝ`.
11. `hbot : ∀ i < n + 1, ∀ x, loss i x ≠ ⊥`.
12. `hdom : ∀ i < n + 1, V ⊆ effectiveDomain (loss i)`.
13. `hlam : 0 < lam`.
14. `hstrong`, the locally let-bound cumulative-objective strong-convexity inequality detailed below.
15. `p : E`.
16. `hp : p ∈ V`.
17. `hprediction`, the prefix-plus-hint minimization inequality detailed below.
18. `g : E →L[ℝ] ℝ`.
19. `hdifference`, the affine lower-support inequality detailed below.
20. `q : E`.
21. `hq : q ∈ V`.

All named binders after the typeclass instances are explicit. The statement is universal over all these inputs satisfying the assumptions; it does not construct p, q, or g.

## Objective definitions and exact scopes

For explanatory notation only, write

- P_n(x) = (psi(x) : EReal) + sum_{i=0}^{n-1} loss(i,x) + (hint(x) : EReal).
- actualG(x) = (psi(x) : EReal) + sum_{i=0}^{n} loss(i,x) + extendedIndicator(V,x).

The header actually names this second objective `G`, not `actualG`. It has TWO separate, identical local `let G : E → EReal := ...` bindings: one inside the TYPE of `hstrong`, and another in the conclusion after the final colon. Neither is an extra theorem argument, and the first local binding does not extend to the second. The descriptive name `actualG` here identifies their common defining expression.

The syntax `sum i in range k` (rendering `∑ i ∈ range k`) ranges over i < k. Thus prediction uses `range n`, while actualG and its strong-convexity assumption use `range (n + 1)`. At n = 0 the prediction sum is empty, whereas actualG includes loss 0. actualG includes loss n and no hint term; P_n includes hint and excludes loss n. The indicator equals zero on V and top outside V. All objective sums/additions and the strong-convexity inequality are in EReal; the explicit real scalar expressions are cast where shown.

## Assumptions, fully expanded

- V is convex for real scalar combinations.
- For every natural i with i < n + 1 and EVERY x : E, loss(i,x) is not bottom. This is a global-in-x condition, not merely a condition on V.
- For every i < n + 1 and x in V, loss(i,x) < top. This follows by expanding the supplied definition of effectiveDomain, not by identifying the domain with a separate finite-value definition.
- lam is strictly positive.
- With the local objective G = actualG, for every x in V, every y in V, and every real a satisfying 0 < a and a < 1:

  G(a • x + (1-a) • y) ≤ (a : EReal) * G(x) + ((1-a : ℝ) : EReal) * G(y) - (((lam/2) * a * (1-a) * ‖x-y‖² : ℝ) : EReal).

  The quantifier order is x, x-membership, y, y-membership, a, positivity of a, upper bound on a. Only interior weights are required explicitly. The squared norm is the given AMBIENT norm of E, and the coefficient is lam/2. No differentiability or separate strong convexity of psi, hint, or individual losses is assumed.
- p belongs to V. Separately, hprediction states: for every z in V, P_n(p) ≤ P_n(z). This is minimization of the prefix-plus-hint objective in EReal. IsMinOn itself does not supply membership.
- g is a continuous real-valued linear functional on E.
- For every z in V:

  (loss(n,p)).toReal - hint(p) + g(z-p) ≤ (loss(n,z)).toReal - hint(z).

  This is a REAL inequality supporting the function x ↦ (loss(n,x)).toReal - hint(x) at p along V. It neither identifies g as a gradient nor asserts differentiability, global support outside V, or convexity of that difference.
- q belongs to V. q is otherwise arbitrary; it is not assumed to minimize G, P_n, or any other objective.

## Conclusion

With a fresh local binding G = actualG, the theorem asserts the REAL inequality

(G(p)).toReal - (G(q)).toReal ≤ ‖g‖² / (2 * lam).

The norm of g is its continuous-linear-map OPERATOR norm induced by the given norm on E and absolute value on ℝ. It is the dual norm in that precise sense, not the ambient norm of a vector representing g. No inner product, Hilbert structure, finite-dimensionality, completeness, or dual-vector identification appears among the binders.

Since q is an arbitrary member of V, this is an upper bound on the objective gap from p to any feasible comparator, conditional on all the displayed assumptions. It is not an asserted absolute-value bound, a distance bound, a lower bound on the gap, an existence theorem for a minimizer, or a regret-sum conclusion. The gap may be negative. No minimization of G by p is assumed.

## Finiteness, positivity, and edge cases

EReal.toReal maps BOTH infinities to zero, so in general it cannot be read as preserving extended-real arithmetic or order. Here hbot and hdom together make every loss i x finite for i ≤ n and x in V. psi and hint already have real values. On V the indicator is zero, so the finite sums defining G and P_n are finite. In particular all uses of toReal in hdifference and the conclusion are at finite values because p, q, and the quantified z lie in V. Convexity of V also puts a • x + (1-a) • y in V under the weights in hstrong. These finiteness observations are consequences of the supplied assumptions, not additional binders or a claim that any proof body was checked.

Off V, hdom gives no exclusion of top, and the indicator is top. No real-valued interpretation of the off-V objective is needed for the stated conclusion; do not infer arithmetic cancellation with infinities there.

V may be specified as any set at the start, and the convexity/strong-convexity universal clauses alone can be vacuous for an empty V. The full theorem's premises hp and hq make an instantiated application with empty V impossible. Nonemptiness is therefore witnessed by the supplied p (and q), rather than given as a separate existence conclusion or Nonempty binder.

lam > 0 entails 2 * lam > 0, so the denominator in the conclusion is strictly positive. The norm square is nonnegative, giving a nonnegative right side. n needs no positivity assumption; n = 0 is permitted. The conditions on i constrain only indices 0 through n and make no claim about later losses.
