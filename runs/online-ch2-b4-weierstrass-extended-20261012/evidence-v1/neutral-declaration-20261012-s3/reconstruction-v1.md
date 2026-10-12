# Independent blind reconstruction: source_weierstrass_extended

## Scope and verified inputs

Only this packet's authorized `declaration-v1.txt` and `definition-context-v1.txt` were used to reconstruct this statement. No proof, import, source paper, review, or other packet is used as evidence. No Lean execution occurred. This is a header interpretation, not a compilation, proof-validity, or source-faithfulness finding.

- declaration-v1.txt SHA256: d4c5943a651e2e72deef8d8380f933d98fe7ae06a9739b7586e31d4a08f2c0c6
- definition-context-v1.txt SHA256: 62e25fe95c839337217ce0e5de2d8c00e6999f2be5663cea57834e125dd3a4e3

## All binders in order

1. Implicit X : Type*.
2. Instance TopologicalSpace X.
3. Instance T2Space X (Hausdorff).
4. Explicit f : X → EReal.
5. Explicit V : Set X.
6. Explicit hf : LowerSemicontinuous f.
7. Explicit hV : IsCompact V.
8. Explicit hdom : (V ∩ effectiveDomain f).Nonempty.

There are no norms, linear structures, finite-dimensionality assumptions, properness assumptions, or convexity assumptions in this header. Lower semicontinuity is global on X in its given topology, with the supplied EReal order-topology interpretation. Compactness is required of the feasible set V, not of the entire space X.

## Exact mathematical content

For every Hausdorff topological space X, every extended-real function f on X, and every compact subset V of X: if f is lower semicontinuous and there exists x∈V satisfying f(x)<top, then there exists p∈V such that, for every z∈V, f(p)≤f(z).

In fully expanded logical form, the domain premise is

    ∃ x : X, x ∈ V ∧ f x < ⊤,

and the conclusion is

    ∃ p : X, p ∈ V ∧ (∀ z : X, z ∈ V → f p ≤ f z).

The header's notation `∃ p ∈ V, ...` supplies membership separately from IsMinOn. All comparisons are in EReal; no toReal conversion or ordinary-real-valued minimum is asserted.

## Consequences and edge cases

The premise implies V is nonempty and excludes f being identically top on V. It does NOT require a finite real-valued point: effectiveDomain is defined using f(x)<top, so a bottom-valued point satisfies it. There is no condition excluding bottom anywhere. The attained minimum may therefore equal bottom. Given the non-top witness x, the minimizer satisfies f(p)≤f(x)<top, so p lies in effectiveDomain f as a consequence; this domain-membership fact is not an explicit second predicate in the written conclusion.

V may contain points where f is top. Values outside V may also be top or bottom, subject to global lower semicontinuity. If V is empty, hdom cannot be supplied. If X is empty, hdom likewise cannot be supplied. No uniqueness, finite minimum, computable construction, quantitative bound, differentiability, or minimization over all of X is claimed.

## Ambiguities and evidence limits

The short theorem name is visible; an enclosing namespace, if any, is absent from the supplied declaration and cannot be recovered. The supplied context explains lower semicontinuity semantically but gives no internal implementation; this reconstruction uses that stated meaning. There is no material ambiguity in the displayed binder or quantifier scopes. Headers alone give no evidence of proof correctness, compilation, provider/helper use, or correspondence with a particular external theorem.
