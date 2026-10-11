# Strong-convex source interface: readiness proposal

The literal source interface is finite on V. Definition 4.1 (printed34/PDF46) says proper f, lambda >= 0, a chosen norm, and convex V subset dom f. Thus D = V intersect dom f equals V. The earlier arbitrary-D readiness proposal needs this explicit qualification before any new header freezes.

For every x,y in V and alpha in (0,1), the source inequality is

    f(alpha*x+(1-alpha)*y)
      <= alpha*f(x)+(1-alpha)*f(y)
         - (lambda/2)*alpha*(1-alpha)*norm(x-y)^2.

Under global no-bottom, convex V and V subset effectiveDomain f, this is mathematically equivalent to Mathlib StrongConvexOn V lambda f.toReal. This is a proposed bridge, not an existing compiled theorem. Mathlib uses a,b >= 0, a+b=1 and subtracts a*b*(lambda/2*norm(x-y)^2). Interior weights match; zero-weight endpoints are identities. Convexity keeps segment points in V, and domain membership plus no-bottom makes every conversion finite. The norm must be the same norm. General real normed E is an explicit generalization of the source R^d, requiring neither Hilbert geometry nor finite dimension for this bridge.

For arbitrary V, the smaller D interface is a declared extension/restriction, not literal equivalence on V. Convex D must be justified: existing extended convexity gives convex effective domain, then intersection with convex V works. Properness and closedness alone do not. SourceProper retains a finite witness somewhere; restricted properness requires a finite witness in V. The indicator of {0} restricted to V={1} demonstrates the missing condition. Unrestricted toReal is unsafe: a constant-top function on a singleton satisfies the vacuous real strong-convex condition for every coefficient while failing properness.

Top outside V and closedness are not assumptions of Definition4.1. They may be needed by later algorithm contracts but are unnecessary for this finite-domain equivalence. Lemma4.2 (PDF46–47) uses V subset dom(partial f) for its support characterization; proper/closed data alone do not supply that qualification. The direct bridge and a segment proof of minimum growth avoid introducing support as a premise. AppendixA.3 (PDF303) requires compactness for its attainment theorem; arbitrary closed unbounded V is insufficient. A.1 needs interior-domain points and has no role in this direct bridge.

The next substantive endpoint remains attained-minimum quadratic growth: from the source strong-convex inequality and a finite attained minimizer p, conclude f(p).toReal+(lambda/2)*norm(q-p)^2 <= f(q).toReal for q in the finite convex domain. Growth is the desired conclusion, never an assumption. The segment argument can approach p using positive weights and an elementary real inequality argument. This report neither proves nor freezes that theorem. Actual selector/attainment, cumulative EReal identities, support where the eventual route uses it, and terminal corrected bounds remain open AND dependencies.

Reusable definitions and ordinary-convex bridges are in OnlineConvexExtended; SourceProper is in OnlineClosedProper; sourceProper_of_domain is in OnlinePrescientBregmanSource. Their current RAW bindings and exact declarations are in the JSON. No reuse claim here asserts new acceptance or proof-term necessity.

Personally inspected rendered pixels: PDF21/28/46/47/303 (printed9/16/34/35/291). JSON records exact PDF, text and PNG hashes. Source text and source-derived interface reasoning are separated there. Requested actor /root/adaptive_decoder, GPT-6 Astra/medium, runtime not attested; source-exposed review. No new BODY, build, header freeze or canonical change. Chapter2 remains partial, seven containers and six future claims open; denominator null.
