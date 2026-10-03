# Source-blind mathematical reconstruction

Actor: `/root/closed_blind`, a distinct decoder agent assigned GPT-6 Astra medium.

Read inventory: only `E:/ABRL/worktrees/research-online-book/runs/online-closed-proper-20261003/blind-packet.txt`. No imported module, source text, source identity, other file, or earlier verdict was inspected.

## Ambient setting and quantifiers

The declarations range over every type E equipped with a topological space structure. There is no stated nonemptiness, separation, metric, vector-space, convexity, or finite-dimensional hypothesis on E. The function f is arbitrary from E to the extended real numbers EReal, whose values include negative infinity (bottom) and positive infinity (top). The set V is an arbitrary subset of E. Statements are universally quantified over the indicated E, its topology, and f or V.

## Definitions

1. `SourceClosed f` means: for every finite real number r, the sublevel set {x in E : f(x) <= r} is closed in E. The threshold quantifier is over the ordinary reals, embedded in EReal; it does not directly quantify over either infinite threshold. No epigraph or convexity condition appears in this definition.

2. `SourceProper f` means the conjunction of (a) for every x in E, f(x) is not negative infinity, and (b) there exist x in E and a finite real number r such that f(x) = r. Thus f takes at least one finite value, may take positive infinity elsewhere, and never takes negative infinity. This is stronger than merely saying that f is not identically positive infinity if negative infinity values were otherwise permitted. It forces E to be nonempty and is false on an empty domain.

The packet additionally supplies the auxiliary function `extendedIndicator V`: it equals the finite value 0 at points of V and positive infinity at points outside V. This is an extended-valued indicator, not a function taking the values 0 and 1.

## Three theorem statements

### `sourceClosed_iff_lowerSemicontinuous`

For every such E and f, all finite-real sublevel sets of f are closed if and only if f is lower semicontinuous.

The referenced predicate `LowerSemicontinuous` is imported rather than expanded in the packet. Under its usual extended-real order/topology meaning, lower semicontinuity says that near each x, f remains strictly above any extended-real a strictly below f(x). Equivalently, each strict superlevel set {x : a < f(x)} is open, for every a in EReal; equivalently, all EReal-threshold sublevel sets are closed. The theorem therefore asserts that checking only finite real thresholds suffices, including at infinite function values.

At threshold positive infinity, the sublevel set is all E, hence automatically closed. At threshold negative infinity, it is {x : f(x) = negative infinity}, which is the intersection over finite real r of the finite sublevel sets. It is therefore closed when SourceClosed holds. Negative infinity values are allowed by SourceClosed; properness is not a premise. At a point with f(x) = positive infinity, lower semicontinuity requires eventual strict lower bounds above every finite real threshold. At a point with f(x) = negative infinity, its pointwise strict-lower-bound condition has no thresholds below that value. On an empty domain both sides hold vacuously. Constant positive-infinity and constant negative-infinity functions satisfy SourceClosed.

### `sourceClosed_indicator_iff`

For every subset V of E, the extended indicator of V has closed sublevel sets for all finite real thresholds if and only if V is closed in E.

For finite r < 0 its sublevel set is empty. For finite r >= 0 its sublevel set is exactly V. In particular the threshold r = 0 detects V, while all other finite thresholds add no distinct closedness obligation. At the extended threshold negative infinity its sublevel set is empty; at positive infinity it is all E. There is no requirement that V be nonempty. The empty set and all E are both closed and give SourceClosed indicators; an empty ambient domain also satisfies this equivalence.

### `sourceProper_indicator_iff`

For every subset V of E, the extended indicator of V is SourceProper if and only if V is nonempty.

The indicator never equals negative infinity. Its finite-value witness exists exactly at a point of V, where the value is 0. If V is empty the indicator is identically positive infinity and is not proper. If V = E it is proper exactly when E is nonempty. When E is empty, every V is empty and both sides of this equivalence are false. Closedness of V is not required. Although a topology is present in the surrounding context, no topological property is used in the meaning of this properness equivalence.

## Context ambiguity and limits

The two principal predicates and the auxiliary indicator are explicitly defined, so their threshold ranges and boundary behavior are determined by the packet. `LowerSemicontinuous`, `EReal`, and `IsClosed` are referenced through imports; their implementations were deliberately not inspected. The explanation of lower semicontinuity uses the standard mathematical reading of that imported predicate and does not independently verify its exact library definition. The imports do not themselves supply additional stated mathematical hypotheses. The packet does not identify any external source or its conventions, and this reconstruction makes no source-fidelity verdict and no compilation or proof-validity claim.
