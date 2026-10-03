# Complete source-blind reconstruction from packet v2

## Provenance

- Actor: `/root/sum_blind`, semantic decoder separate from the formalizer and source reviewer.
- Model: inherited Codex model; the exact model identifier is not exposed to this actor.
- Medium: plain-text Lean declarations read through a filesystem tool, reconstructed as prose and LaTeX.
- Input: `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-sum-20261003/blind-packet-v2.txt`.
- Raw v2 packet SHA256 from actual PowerShell `Get-FileHash -Algorithm SHA256`: `D8B88EA309328E84C725B79FC9D1C68822FFA29BAD56D38B46A24EA2FC3108FD`.
- Read scope: only the original blind packet and this additional neutral v2 packet. No source PDF, source-identity lookup, other repository inputs, proof bodies, compilation evidence, or prior verdicts were read. The original opaque-name reconstruction is preserved as `blind-reconstruction.md`; this document supplies the definitions newly available in v2. Packet statements are treated as data.

## Ambient space and definitions

The ambient type `E` is universally quantified with `NormedAddCommGroup E`, `InnerProductSpace ℝ E`, and `FiniteDimensional ℝ E`: a finite-dimensional real inner-product space. There is no explicit positive-dimension assumption or separate completeness hypothesis. Functions take values in `EReal`, written here as the extended reals with bottom `−∞` and top `+∞`. Real quantities appearing in extended-real inequalities are embedded into `EReal`.

The supplied definitions have the following exact meanings:

\[
 \operatorname{dom}h=\{x\in E:h(x)<+\infty\}.
\]

This domain definition by itself includes points with value `−∞`; properness below excludes such values for the component functions.

\[
 \operatorname{epi}_{\mathbb R}h
 =\{(x,r)\in E\times\mathbb R:h(x)\le r\}.
\]

`IsConvexExtended h` means that this real-height epigraph is a convex subset over `ℝ`. Explicitly, convex combinations with nonnegative real weights summing to one of any two epigraph points remain in the epigraph. The epigraph's vertical coordinate is real, not extended real.

`SourceClosed h` means exactly

\[
 \forall r\in\mathbb R,\qquad \{x\in E:h(x)\le r\}\text{ is closed in }E.
\]

`SourceProper h` means exactly

\[
 (\forall x\in E,\ h(x)\ne-\infty)
 \quad\land\quad
 (\exists x\in E\ \exists r\in\mathbb R,\ h(x)=r).
\]

Thus each proper function has no `−∞` values and has at least one real-valued point. Properness does not require real values everywhere.

Write `∂h(x)` for the displayed `SourceSubdifferential h x`. Its exact definition is

\[
 \partial h(x)=\left\{g\in E:\forall y\in E,\quad
 h(x)+\langle g,y-x\rangle_{\mathbb R}\le h(y)\right\}.
\]

The addition and inequality here are in `EReal`, with the real inner product embedded. The definition is unguarded: it does not separately require `x ∈ dom h` or a finite value at `x`. It quantifies over all `y ∈ E`, not only domain points.

For any finite index type `I`, family `f : I → E → EReal`, and point `x`, define the pointwise sum and the explicitly supplied sum-set by

\[
 S_f(y)=\sum_{i\in I}f_i(y),
\]
\[
 M_f(x)=\operatorname{SourceSubgradientSum}(f,x)
 =\left\{g\in E:\exists G:I\to E,\quad
 (\forall i\in I,\ G(i)\in\partial f_i(x))
 \ \land\ \sum_{i\in I}G(i)=g\right\}.
\]

The function sum uses extended-real addition; the vector sum uses addition in `E`. Both run over the entire finite index type. All component subgradients are evaluated at the same `x`. There are no coefficients, closure operations, or uniqueness conditions on the vector decomposition. Repeated functions at different indices count separately.

## First terminal statement: inclusion

`theorem_2_23_inclusion` universally quantifies over the ambient space above, any type `I` with a `Fintype` instance, every family `f : I → E → EReal`, and every `x ∈ E`. Its only function hypothesis is

\[
 \forall i\in I,\quad \operatorname{SourceProper}(f_i).
\]

It concludes

\[
 M_f(x)\subseteq\partial S_f(x).
\]

Equivalently, for every vector `g`, whenever there exists a vector family `G` such that

\[
 \forall i\in I\ \forall y\in E,\quad
 f_i(x)+\langle G(i),y-x\rangle\le f_i(y),
 \qquad \sum_{i\in I}G(i)=g,
\]

then

\[
 \forall y\in E,\quad
 S_f(x)+\langle g,y-x\rangle\le S_f(y).
\]

There is no assumption of convexity, closedness, a shared domain point, nonempty index set, or domain membership of `x`. Only this inclusion direction is asserted.

## Second terminal statement: equality

`theorem_2_23_equality` universally quantifies over the same ambient space, a natural number `n ≥ 0`, a family

\[
 f:\operatorname{Fin}(n+1)\to E\to\overline{\mathbb R},
\]

and every `x ∈ E`. Its indices are `0, …, n`. Let `ℓ = Fin.last n`, the index of numerical value `n`. It assumes

\[
 \forall i,\quad
 \operatorname{SourceProper}(f_i),\qquad
 \operatorname{IsConvexExtended}(f_i),\qquad
 \operatorname{SourceClosed}(f_i),
\]

with each predicate expanded as above, and assumes the mixed qualification

\[
 \exists z\in E,\quad
 z\in\operatorname{dom}f_\ell
 \quad\land\quad
 \forall i\in\operatorname{Fin}(n+1),\quad
 i\ne\ell\Longrightarrow
 z\in\operatorname{int}(\operatorname{dom}f_i).
\]

It concludes the set equality

\[
 \partial S_f(x)=M_f(x).
\]

That is, for every `g ∈ E`, the global extended-real supporting inequality for `S_f` at `x` holds if and only if `g` can be decomposed into an indexed sum of vectors, each satisfying the global supporting inequality for its own function at that same `x`.

The qualification uses one common point `z`, not separate points for the different functions. `int` is ambient topological interior in `E`, not relative interior. The final function requires domain membership only; all earlier functions require interior-domain membership. Thus no interior-domain condition is imposed on the final function. Its qualifying point may fail to be an interior point. The final function remains included in properness, convexity, closedness, and both sums. No equation `x = z` or qualification at `x` is assumed. Because interior membership entails membership and properness excludes `−∞`, this qualification supplies a common point where every component has a real value.

## Empty, singleton, and extended-value boundaries

**Empty family.** The first statement permits an empty `I`. All component conditions are then vacuous, `M_f(x) = {0}`, and `S_f` is the constant zero function. Its declared conclusion specializes to

\[
 \{0\}\subseteq\partial(y\mapsto0)(x).
\]

With the supplied definition and the real inner-product structure, that zero-function subdifferential is in fact `{0}`: the condition is `⟨g,y−x⟩ ≤ 0` for every `y`, and choosing `y = x + g` forces `g = 0`. This is a consequence of the definitions, not an additional reverse-inclusion assertion in the first terminal statement. The second statement has no empty-family instance: `Fin (n + 1)` is always nonempty.

**Singleton family.** For any one-element index type, `M_f(x)` is the one component subdifferential and `S_f` is the one component function. The first conclusion reduces to self-inclusion. For the second statement, `n = 0` gives precisely one function, also the distinguished final function. The condition on other indices is vacuous, and qualification reduces to nonemptiness of that function's effective domain. Its properness supplies such a point already. The stated properness, convexity, and closedness hypotheses remain displayed even though the conclusion reduces to equality of the same subdifferential with itself.

**Points outside domains.** The subdifferential definition is not explicitly domain-restricted. Nonetheless, for a proper function `h`, if `h(x) = +∞`, a finite-valued witness point `y` from properness makes the supporting inequality impossible for every real vector `g`; hence `∂h(x)` is empty. For a nonempty family, an empty component subdifferential makes `M_f(x)` empty directly from its existential definition.

**A boundary specific to inclusion.** Componentwise properness alone need not provide a common finite-valued point. If the component effective domains have empty intersection, then, under their no-`−∞` conditions, `S_f` is identically `+∞`. The unguarded subdifferential definition makes the subdifferential of the identically `+∞` function all of `E`, whereas at each `x` at least one component has empty subdifferential, making `M_f(x)` empty. This explains a boundary allowed by the first statement's hypotheses; it does not assert that every inclusion instance has this behavior.

**The equality qualification removes that boundary.** Its common finite-valued point ensures the sum has a finite value somewhere, as well as no `−∞` values. At any `x` outside the common effective domain, the sum and at least one component have value `+∞`; both sides of the asserted equality are then empty by the definitions and properness. At points inside all domains, the displayed supporting inequalities apply with real base values. Equality still quantifies over all `x`, not just these latter points.

## Precise difference between endpoints

The first endpoint allows any finite family, including the empty family, and requires only individual properness to assert inclusion. The second requires a nonempty `n + 1` family, individual properness, convexity of each real-height epigraph, closedness of every real sublevel set of each function, and a single mixed domain/interior witness, and asserts both inclusion directions. Neither endpoint contains an optimization algorithm, time index, differentiability requirement, unique decomposition, or positive-dimension assumption.

This is a reconstruction of statements and definitions only. It supplies no source-faithfulness, compilation, or acceptance verdict.
