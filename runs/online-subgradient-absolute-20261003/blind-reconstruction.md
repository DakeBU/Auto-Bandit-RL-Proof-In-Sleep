# Source-blind mathematical reconstruction

This reconstruction uses only `blind-packet.txt`. It identifies no external source and makes no source-fidelity, compilation, proof-validity, or external-human-review claim. The declarations are reconstructed as stated; no proof bodies were supplied.

Independently computed raw-file SHA256 (PowerShell `Get-FileHash`, without text normalization):

`C6716ADBFEDFCA95081CC1B98A721FBF08BE4F9683A6EF0F2332BF1231761E3D`

## Seven semantic slots

1. **Objects and scalar specialization.** The function is the real absolute value, embedded as a finite extended real: \(f:\mathbb R\to\overline{\mathbb R}\), \(f(t)=|t|\). The point \(x\), candidate support slope \(g\), and comparison point \(y\) are all real numbers. The final theorems concern this fixed scalar function, not arbitrary functions or arbitrary vector spaces.

2. **Supporting-set definition.** In this specialization the supplied definition is exactly
   \[
   S(x):=\{g\in\mathbb R:\ \forall y\in\mathbb R,\ |x|+g(y-x)\le |y|\}.
   \]
   The packet's inner product becomes ordinary real multiplication. Because every value in this inequality is finite, the extended-real notation gives the same inequality as the displayed real inequality. Each \(g\in S(x)\) defines an affine function touching \(|\cdot|\) at \(x\) and lying below it everywhere.

3. **Quantifiers and global comparison domain.** The combined theorem quantifies over every \(x\in\mathbb R\). Membership quantifies over every comparison point \(y\in\mathbb R\), including points on either side of zero and outside any neighborhood of \(x\). Equality of sets quantifies over every candidate \(g\in\mathbb R\). Thus it is a global supporting condition on the whole ambient real line, without a constrained feasible set or a local-only comparison.

4. **Assumptions and the three leaves.** The positive leaf has exactly \(x\in\mathbb R\) and \(0<x\), and concludes \(S(x)=\{1\}\). The zero leaf fixes \(x=0\), has no additional premise, and concludes \(S(0)=[-1,1]\). The negative leaf has exactly \(x\in\mathbb R\) and \(x<0\), and concludes \(S(x)=\{-1\}\). No smoothness premise, bounded-domain premise, step size, random event, or auxiliary parameter appears in these statements.

5. **Exact sets and constants.** The positive singleton is exactly \(\{+1\}\), and the negative singleton is exactly \(\{-1\}\). The zero interval is closed at both ends: \(\{g\in\mathbb R:-1\le g\le1\}\). In particular, \(-1\), \(0\), and \(1\) are all allowed at zero, as is every real slope between the endpoints; slopes outside that interval are excluded.

6. **Branch boundaries and all-point assembly.** The nested conditional tests \(0<x\) first, then \(x=0\) when the first test fails. Its final branch therefore means \(\neg(0<x)\land x\ne0\), equivalent over \(\mathbb R\) to \(x<0\). The three cases are mutually exclusive and exhaust the entire real line. Zero belongs only to the closed-interval case; neither strict-sign leaf includes zero.

7. **Logical strength, scope, and gaps.** Every equality is an exact characterization with necessity and sufficiency, not merely the construction or selection of one valid slope. At zero, proving that \(g=0\) supports the function would be strictly weaker than the supplied assertion. There is no gap in the real-point case partition. The packet does not provide proof bodies, a source reference, or the implicit typeclass context for its generic definition, so it does not let this review establish compilation, source coverage, or the complete general-space interface.

## Plain-language statement and fully quantified form

At each real point, all globally supporting slopes of the absolute-value function are precisely as follows: the only slope is \(+1\) at a strictly positive point, every slope in the closed interval from \(-1\) through \(+1\) is allowed at zero, and the only slope is \(-1\) at a strictly negative point.

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

The three individual leaves can be expressed without set notation as

\[
\forall x\in\mathbb R,\quad x>0\Longrightarrow
\Bigl[\forall g\in\mathbb R,\quad
(\forall y\in\mathbb R,\ |x|+g(y-x)\le |y|)\iff g=1\Bigr],
\]
\[
\forall g\in\mathbb R,\quad
(\forall y\in\mathbb R,\ gy\le |y|)\iff (-1\le g\land g\le1),
\]
\[
\forall x\in\mathbb R,\quad x<0\Longrightarrow
\Bigl[\forall g\in\mathbb R,\quad
(\forall y\in\mathbb R,\ |x|+g(y-x)\le |y|)\iff g=-1\Bigr].
\]

## Interface ambiguity

The neutral definition writes `E` without declaring its implicit parameters or typeclasses. Its subtraction and real inner product require suitable ambient structure, but the exact full general-space assumptions cannot be recovered from this abbreviated interface alone. It would be unjustified to claim a theorem about all such spaces from this packet. This omission does not make the four displayed statements ambiguous: each explicitly specializes the function and evaluation point to the real line, and the packet explicitly specifies how its inner product and finite extended-real embedding are interpreted. In particular, the universal `y` in those specializations ranges over all real numbers.
