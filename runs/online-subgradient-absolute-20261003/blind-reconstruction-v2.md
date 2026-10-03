# Source-blind reconstruction: packet v2

## Read scope and identity

During this revision I read only `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-20261003/blind-packet-v2.txt`. I did not inspect the imported file, proof bodies, external sources, source identity, other reviews, or any other file. I did not search the internet. The previous blind reconstruction remains in conversational context, but this v2 reconstruction is based on the mathematical interface actually supplied by the v2 packet. This is an AI source-blind semantic reconstruction, not an external-human review or a source approval.

I independently measured the packet's raw bytes with PowerShell `Get-FileHash -Algorithm SHA256`, without text or newline normalization:

`9D65343F308BB4BAE9A569AFB88C0F94240F8A35B523D71AE74AFBF0FB1A1156`

## Seven semantic slots

1. **Generic context and actual specialization.** The definition has implicit type `E : Type*`, with `[NormedAddCommGroup E]` and `[InnerProductSpace ℝ E]`. Thus its ambient space is a real inner-product space with the supplied normed additive group structure; no completeness or finite-dimensionality assumption is displayed. It accepts any `f : E → EReal` and `x : E` and returns `Set E`. The four actual theorem statements specialize to the real scalar line and the fixed finite-valued absolute-value function \(f(t)=|t|\), embedded in the extended reals. They are not arbitrary-space absolute-value theorems.

2. **Supporting relation.** The generic set is
   \[
   \partial_s f(x)=\{g\in E:\forall y\in E,\ f(x)+\langle g,y-x\rangle_{\mathbb R}\le f(y)\},
   \]
   where the inner-product value is embedded in `EReal`. In the actual scalar statements this reduces exactly to
   \[
   S(x)=\{g\in\mathbb R:\forall y\in\mathbb R,\ |x|+g(y-x)\le |y|\}.
   \]
   All values in this specialized inequality are finite, so it is equivalently the ordinary real inequality displayed here.

3. **Quantifiers and domain.** The combined statement holds for every \(x\in\mathbb R\). Set equality concerns every candidate \(g\in\mathbb R\). The supporting inequality must hold for every \(y\in\mathbb R\), on the whole ambient line, including points across zero. There is no restriction to a neighborhood, sign region, bounded interval, or feasible subset.

4. **Leaf assumptions.** The positive leaf assumes only \(x\in\mathbb R\) and \(0<x\). The zero leaf fixes the evaluation point to \(0\), with no additional premise. The negative leaf assumes only \(x\in\mathbb R\) and \(x<0\). No additional hypotheses about differentiability, convexity, boundedness, or parameters occur in the stated scalar leaves.

5. **Exact outputs and endpoints.** The positive leaf gives exactly \(S(x)=\{1\}\); the zero leaf gives exactly \(S(0)=[-1,1]=\{g:-1\le g\land g\le1\}\); the negative leaf gives exactly \(S(x)=\{-1\}\). Both endpoints at zero are included. Zero itself and every slope between the endpoints are included at zero, and every slope outside that interval is excluded.

6. **Branch boundaries and assembly.** The combined statement first tests \(0<x\). If that fails, it tests \(x=0\). The final branch therefore has \(\neg(0<x)\land x\ne0\), equivalent on the real line to \(x<0\). The branches are mutually exclusive and exhaustive. Neither strict-sign branch includes zero. There is no missing point or boundary case.

7. **Logical strength and evidential scope.** These are exact characterizations of the entire supporting set, with both necessity and sufficiency. They do not merely exhibit or select one supporting slope. In particular, selecting slope zero at the origin would not establish the closed-interval characterization. The packet supplies statements and an interface, not proof bodies; this reconstruction establishes their meaning, not compilation, proof correctness, or fidelity to an unidentified external source.

## Complete scalar theorem and three leaves

For every real point, the globally supporting slopes of absolute value are exactly the following:

\[
\forall x\in\mathbb R,\qquad
\{g\in\mathbb R:\forall y\in\mathbb R,\ |x|+g(y-x)\le |y|\}
=
\begin{cases}
\{1\},&x>0,\\
[-1,1],&x=0,\\
\{-1\},&x<0.
\end{cases}
\]

Equivalently, the individual leaves assert:

\[
\forall x\in\mathbb R,\quad x>0\Longrightarrow
\Bigl[\forall g\in\mathbb R,\quad
(\forall y\in\mathbb R,\ |x|+g(y-x)\le|y|)\iff g=1\Bigr],
\]
\[
\forall g\in\mathbb R,\quad
(\forall y\in\mathbb R,\ gy\le|y|)\iff(-1\le g\land g\le1),
\]
\[
\forall x\in\mathbb R,\quad x<0\Longrightarrow
\Bigl[\forall g\in\mathbb R,\quad
(\forall y\in\mathbb R,\ |x|+g(y-x)\le|y|)\iff g=-1\Bigr].
\]

In plain language, there is just one globally supporting slope at a positive point, namely plus one, and just one at a negative point, namely minus one. At the origin the complete set of globally supporting slopes is the closed interval from minus one to plus one.

## Ambiguity assessment and preserved boundaries

The v2 packet explicitly supplies the previously absent generic type and typeclass context, so that context omission is resolved. The generic `E` and the fixed scalar specialization are now clearly distinguished. I find no remaining ambiguity in the real scalar supporting-set characterization, constants, quantifiers, whole-ambient comparison domain, or case boundaries. An unprovided proof or unidentified source is an evidential limitation, not an ambiguity in these statements.

This revision writes only this new reconstruction file. The original packet and reconstruction were not modified; no proofs or source files were edited or compiled. The new raw hash binds this reconstruction to the v2 packet only.
