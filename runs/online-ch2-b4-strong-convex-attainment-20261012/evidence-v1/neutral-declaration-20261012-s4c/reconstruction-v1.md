# Blind statement reconstruction: halfline_quadratic_unique_attainment

Scope: interpretation of this packet's two authorized inputs only. No proof, source, imports, reviews, or Lean execution. No proof/provider-use or source-acceptance claim.

Verified SHA256: declaration-v1.txt = d786d31b4e8582ba4977060e5c662cc0a386703289b22122496e078d590dcf87; definition-context-v1.txt = 910e6e40db16c31ac9a4660ee5e83b575aaf8c74f5e2ffbc583497def61b2191.

## Ambient definitions and binders

E is the real Euclidean inner-product space with one coordinate indexed by Fin 1. A point x is determined by its real coordinate x 0, its norm is |x 0|, and point(t) has sole coordinate t. coordinates is the identity algebraic real linear equivalence on E; it is defined in the context but does not appear in the proposition. Let Q=quadratic. Q(x) embeds (x 0 - 2)^2/2 in EReal when x 0≥0, and is top otherwise. The context also defines affine(x) as the embedded coordinate x 0, but affine is unused here.

D=effectiveDomain Q means {x | Q(x)<top}. This generic domain definition includes bottom-valued points, but Q never takes bottom. SourceSubdifferential Q p is the set of vectors g:E such that for every y:E, Q(p)+(inner ℝ g (y-p) embedded in EReal)≤Q(y). IsMinOn Q V p means ∀ q∈V, Q(p)≤Q(q), with membership separate.

There are no external theorem parameters, instance binders, or premises. This is one closed proposition with eight right-associated top-level conjuncts. The unique existential p, universal p, their local comparator q, and the unboundedness variables R and x have separate scopes described below.

## Eight conjuncts in exact order

1. ∃! p:E, p∈D ∧ ∀ q:E, Q(p)≤Q(q). Exactly one point in the effective domain globally minimizes Q over all E. Uniqueness applies to the complete conjunction predicate.
2. ∀ p:E, (p∈D ∧ ∀ q:E, Q(p)≤Q(q)) ↔ p=point(2). This characterizes all points satisfying that same predicate, in both directions. The universal p here is distinct in scope from the first conjunct's unique existential.
3. point(-2)∈SourceSubdifferential Q (point(0)). Expanded: ∀ y:E, Q(point(0))+(inner ℝ (point(-2)) (y-point(0)) embedded in EReal)≤Q(y). Writing t=y 0, the left side embeds 2-2t. For t≥0 the inequality is 2-2t≤(t-2)^2/2; for t<0 the right side is top. The support vector is nonzero, and its basepoint is point(0), not point(2).
4. ¬IsMinOn Q Set.univ (point(0)). Since Set.univ contains every q:E, point(0) is not a global minimizer. This coexists with the subgradient assertion at point(0).
5. ∀ R:ℝ, ∃ x:E, x∈D ∧ R<‖x‖. For each real threshold, a possibly different feasible point has larger Euclidean norm. This is unboundedness of the effective domain in norm. R need not be nonnegative. It does not assert that every feasible point exceeds each threshold, nor that Q has no minimizer.
6. D={x:E | 0≤x 0}. The effective domain is the closed nonnegative coordinate halfline, including its boundary zero.
7. Q(point(2))=(0:EReal).
8. Q(point(-1))=top.

## Interpretation and edge cases

The unique global minimum is attained at point(2) with finite value zero, while negative-coordinate points have top value and lie outside D. The domain is unbounded, yet the minimum exists and is unique. All objective comparisons use EReal order; there is no toReal conversion. The threshold inequality in conjunct 5 is real, and its norm is the ambient Euclidean norm, not an operator norm.

The nonzero subgradient at point(0) is a supporting vector, not a minimizer certificate. Q(point(0))=2 follows from the definition and explains the strict improvement at point(2); that value is not a separate conjunct. SourceProper and SourceClosed are explained in the context but are not asserted as conjuncts or required as external premises here. The definition does give a nowhere-bottom function with a finite point; that properness observation is derived, not an additional displayed clause. No arbitrary dimension, arbitrary function, strong-convexity constant, compact-set hypothesis, iteration, rate, or provider call is part of this closed header.

No enclosing namespace is supplied, so a fully qualified name cannot be recovered. No material ambiguity in the displayed quantifiers or conjunction order remains given the supplied definitions. A theorem header cannot establish compilation, proof correctness, which assumptions a proof used, or invocation of another theorem.
