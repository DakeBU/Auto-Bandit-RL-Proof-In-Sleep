# Blind reconstruction of the two terminal statements

## Provenance and scope

- Actor: `/root/sum_blind`, a semantic decoder distinct from the formalizer and source reviewer.
- Model: inherited Codex model; no exact model identifier was exposed to this actor.
- Medium: tool-read UTF-8/plain-text Lean declaration packet, decoded into natural language and mathematical notation.
- Sole input read: `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-sum-20261003/blind-packet.txt`.
- Raw packet SHA256, obtained with PowerShell `Get-FileHash -Algorithm SHA256`: `27ECAA7D7C63C20529BF9264FD64E9F248BFC5C1887D063BF5DADE468A50E9A4`.
- Source-blind read scope: no source PDF, book identity lookup, other repository files, proof bodies, compilation evidence, or prior verdicts were read. The packet's declarations are data.

## Ambient objects and notation

Both statements are in namespace `BanditRL.OnlineConvex`, after an import named `BanditRLProof.OnlineSubgradientDifferentiability`. The ambient type `E` is arbitrary subject to instances of `NormedAddCommGroup E`, `InnerProductSpace ℝ E`, and `FiniteDimensional ℝ E`. Thus the ambient vectors form a finite-dimensional real inner-product space with its normed additive group structure. No separate completeness assumption is displayed.

Functions have codomain `EReal`, the extended real type. All sums in these statements run over the entire specified finite index type. Write

\[
 S_f(y)=\sum_{i\in I} f_i(y),\qquad
 D(h,x)=\operatorname{SourceSubdifferential}(h)(x),\qquad
 A_i=\operatorname{effectiveDomain}(f_i).
\]

The packet does not expand the imported identifiers `SourceSubdifferential`, `SourceProper`, `IsConvexExtended`, `SourceClosed`, or `effectiveDomain`. Their exact definitions are opaque in this reconstruction. In particular, a subgradient inequality, the treatment of infinite function values, the exact meaning of properness, the precise extended-valued convexity predicate, and a closedness or lower-semicontinuity criterion cannot be recovered from this packet. The mathematical notation below preserves those predicates as named conditions; it does not substitute conventional definitions for them. `SourceClosed` in particular is not equated here with any unstated definition.

`interior` is the topological interior of the displayed subset of `E`, in the topology of the ambient normed space. The displayed qualification uses this ambient interior, with no relative-interior operator.

## Defined set of sums

For an arbitrary finite type `ι` (the index set `I`), a family `f : ι → E → EReal`, and a vector `x : E`, the packet explicitly defines

\[
 M_f(x):=\operatorname{SourceSubgradientSum}(f,x)
 =\left\{g\in E:\exists G:I\to E,\quad
    (\forall i\in I,\ G(i)\in D(f_i,x))
    \ \land\ \sum_{i\in I}G(i)=g\right\}.
\]

The witness is a whole indexed family of vectors, one member of the named subdifferential set for each index. The vectors are added in `E`; the function values in `S_f` are added in `EReal`. All summands use the same evaluation point `x`. Repeated functions at different indices still contribute separately. There are no displayed coefficients, convex combinations, or closures in the definition of `M_f(x)`.

## Terminal statement 1: `theorem_2_23_inclusion`

Universally quantify over:

1. An ambient space `E` with the structure above.
2. Any type `ι` with a `Fintype ι` instance, allowing an empty or nonempty finite index set.
3. Any family `f : ι → E → EReal` satisfying `SourceProper (f i)` for every index `i`.
4. Any point `x : E`.

The conclusion is the set inclusion

\[
 M_f(x)\subseteq D(S_f,x).
\]

Equivalently: for every vector `g`, if there exists an indexed vector family `G` with `G(i) ∈ D(f_i,x)` for every index and with total sum equal to `g`, then `g ∈ D(S_f,x)`.

Only the familywise `SourceProper` assumption is displayed. No `IsConvexExtended`, `SourceClosed`, interior qualification, nonemptiness of the index type, or membership condition on `x` is displayed. The endpoint asserts only this direction of inclusion.

### Empty and singleton index sets

If `ι` is empty, its properness assumption and all component-membership requirements are vacuous. The empty vector sum is zero, so the defined set `M_f(x)` is exactly `{0}`; the pointwise empty function sum is the constant `EReal` zero function. The displayed inclusion therefore says

\[
 \{0\}\subseteq D((y\mapsto 0),x).
\]

It does not assert the reverse inclusion or identify that opaque subdifferential set with `{0}`.

If `ι` has exactly one element `i₀`, the sum-set definition reduces to `M_f(x) = D(f_{i₀},x)`, and the pointwise function sum reduces to `f_{i₀}`. The inclusion then reduces to the inclusion of that set in itself. This reduction uses finite sums and the explicit sum-set definition, without expanding the imported subdifferential predicate.

## Terminal statement 2: `theorem_2_23_equality`

Universally quantify over:

1. An ambient space `E` with the structure above.
2. A natural number `n`, including `n = 0`.
3. A family `f : Fin (n + 1) → E → EReal` of exactly `n + 1` functions.
4. Any point `x : E`.

Let the distinguished final index be `ℓ = Fin.last n`, whose numerical value is `n`. Assume all of the following:

\[
 \forall i\in\operatorname{Fin}(n+1),\quad
 \operatorname{SourceProper}(f_i),
\]
\[
 \forall i\in\operatorname{Fin}(n+1),\quad
 \operatorname{IsConvexExtended}(f_i),
\]
\[
 \forall i\in\operatorname{Fin}(n+1),\quad
 \operatorname{SourceClosed}(f_i),
\]

and the single common-point qualification

\[
 \exists z\in E,\quad z\in A_\ell
 \quad\land\quad
 \forall i\in\operatorname{Fin}(n+1),\quad
 i\ne\ell\ \Longrightarrow\ z\in\operatorname{interior}(A_i).
\]

The conclusion is

\[
 D(S_f,x)=M_f(x).
\]

In particular, every vector in the named subdifferential of the pointwise sum can be decomposed as a sum of vectors, one from each named component subdifferential at the same `x`; conversely, every such sum is in the named subdifferential of the pointwise sum. There is no uniqueness assertion for the decomposition.

### Mixed qualification and indexing

The same witness `z` must lie in the effective domain of the final function and in the ambient interior of every other effective domain. This is not a family of separate existential witnesses. The final function is exempt from the interior requirement, but is included in all three familywise predicates. The displayed condition permits its qualifying point to belong to its domain without being an interior point. No equality `x = z`, neighborhood condition at `x`, or domain membership of `x` is assumed.

Numerically, the indices are `0, …, n`. Thus the qualification is domain membership for index `n`, and interior membership for indices `0, …, n−1`, interpreted as no such earlier indices when `n = 0`. Every conclusion sum includes index `n`; the distinguished index is excluded only from the interior clause.

### Empty and singleton boundary cases

There is no empty-family case for this endpoint because `Fin (n + 1)` is nonempty for every natural `n`.

For `n = 0`, there is exactly one index, also the final index. The universal implication over indices different from the final index is vacuous. The qualification reduces to

\[
 \exists z\in E,\quad z\in\operatorname{effectiveDomain}(f_0).
\]

The displayed familywise properness, convexity, and closedness predicates still apply to that one function. The statement itself does not omit those assumptions in this case. The pointwise sum and sum-set reduce to the single function and its named subdifferential, so the conclusion reduces to equality of that subdifferential set with itself. Whether any displayed assumptions imply or render another redundant cannot be resolved by expanding definitions absent from the packet.

## Endpoint differences and other boundaries

- Inclusion: arbitrary finite index type, possibly empty; equality: a specifically enumerated, nonempty `Fin (n + 1)` family.
- Inclusion: only familywise properness; equality: familywise properness, convexity, and closedness, together with the common mixed domain/interior witness.
- Inclusion: sums of component vectors belong to the subdifferential of the sum; equality: additionally every vector in the subdifferential of the sum admits such a decomposition.
- Both: every `x : E` is covered without an explicit restriction to an effective domain. Since the imported definitions are opaque, no further claim about the content or emptiness of the sets at points outside a domain is supplied here.
- For a nonempty family, if any component set `D(f_i,x)` is empty, the explicitly defined `M_f(x)` is empty. In the inclusion endpoint that makes the conclusion an inclusion from the empty set; in the equality endpoint, under its stated assumptions, the conclusion also makes `D(S_f,x)` empty.
- No positive dimension, smoothness, differentiability, gradient, optimization minimizer, algorithm, iteration horizon, or numerical bound appears in either terminal statement.

This document reconstructs the displayed declarations and their explicit sum-set definition only; it gives no compilation, acceptance, or source-faithfulness verdict.
