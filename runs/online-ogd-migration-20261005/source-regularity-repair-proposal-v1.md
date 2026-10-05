This is a root mathematical audit proposal, not a compiled counterexample or a
reviewer verdict. Existing sixteen headers, proof bodies and old contracts are
unchanged. No previous review is retroactively attributed to a distinct actor.

The source calls for convex real losses differentiable on an open set containing
V. Current RegularLoss also requires that open neighborhood to be convex because
ConvexOn carries convexity of its set. The source-to-current-predicate implication
requires proof; ordinary local differentiability does not supply it immediately.

A concrete candidate separating the two assumptions is E=R²,
V={(x,0):x in R}, f(x,y)=max(exp(-x),y). The function is globally finite and
convex. On the open set U0={(x,y):y<exp(-x)}, which contains V, f=exp(-x) and is
differentiable. However, any open convex U containing the entire horizontal line
contains some (0,b), b>0. Convexity with (2x,0) puts (x,b/2) in U for every x;
convexity with (x,0) then puts all intermediate heights in U. For sufficiently
large x, 0<exp(-x)<b/2, so U contains (x,exp(-x)). At that point the vertical
restriction is max(exp(-x),y), which is not differentiable. Thus no such U can
be a differentiability neighborhood. All steps need separate source scrutiny;
this text is not Lean compilation evidence.

If confirmed, do not modify or weaken old RegularLoss declarations. Freeze a new
source-premise interface using ConvexOn on V plus DifferentiableAt at points in
V (or the source's arbitrary open differentiability neighborhood). Reuse the
same Domain/project/step/iterate/iterateVariable and actual gradient, not a new
algorithm. The existing shared convex_gradient_lower_bound already accepts the
former local point derivative and convex restriction. It can supply genuine
first-order support, followed by actual projection/norm expansion and cumulative
fixed/variable/tuned endpoints with the original negative residual. Prove the
source hypotheses imply this new interface. Any new targets require fresh
versioned contract and distinct blind/source stabilization before body work.

Projection Proposition2.11 has no RegularLoss assumption and can be semantically
closed independently. Lemma2.12 and old regret statements remain true under
their actual stronger predicate; this fact alone does not close the broader
source obligation. Keep the full source obligation required in the chapter
ledger and explicitly distinguish a source-scope repair from a proof failure.
