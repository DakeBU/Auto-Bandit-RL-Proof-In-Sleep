# Source-blind semantic reconstruction

This report decodes only `blind-packet.txt`. It is an AI semantic reconstruction of unproved headers, not a proof, source comparison, or human/external review. The imported module was not inspected.

## Shared interpretation

The ambient space E is a real inner-product space, with its normed additive group structure. For a function f : E -> EReal and a point x in E, the displayed set is

\[
\partial f(x)=\{g\in E:\ \forall y\in E,\ f(x)+\langle g,y-x\rangle\le f(y)\}.
\]

The real inner product is coerced into the extended reals in this inequality. Both functions occurring in the claims are finite-valued, so their displayed inequalities have the usual real-valued interpretation. Every test point y ranges over the entire ambient space; there is no restricted feasible domain, local neighborhood, or almost-everywhere qualifier.

## Claim 1: seven semantic slots

1. **Ambient objects:** Any real inner-product space E as above. No finite-dimensionality or completeness assumption is stated.
2. **Universally quantified data:** For every a in E, every b in R, and every x in E.
3. **Function and evaluation point:** f(y) = <a,y> + b, embedded in EReal, evaluated at x.
4. **Admissibility assumptions:** There are no additional conditions on a, b, or x. The subgradient definition quantifies over every y in E.
5. **Conclusion and exact quantifier structure:** The full set equality is partial f(x) = {a}. Equivalently, for every g in E,
   \[
   [\forall y\in E,\ \langle a,x\rangle+b+\langle g,y-x\rangle\le\langle a,y\rangle+b]\iff g=a.
   \]
   This asserts both that a satisfies every supporting inequality and that every vector satisfying them equals a.
6. **Boundary and degenerate cases:** If a=0, the function is the constant b and the full subdifferential is {0}. The value of b and the chosen evaluation point do not change the set. A zero-dimensional space is allowed and yields the same singleton statement.
7. **Scope and limitations:** This is a pointwise supporting-inequality characterization for an affine function on the whole space. The header supplies no algorithm, iterative sequence, probability law, optimization bound, or proof. It makes no assertion about a different subdifferential convention or a restricted-domain function.

## Claim 2: seven semantic slots

1. **Ambient objects:** Any finite-dimensional real inner-product space E with the shared normed additive group structure. Finite-dimensionality is an explicit additional hypothesis of this claim, whether or not it could be weakened in a different theorem.
2. **Universally quantified data:** For every z in E and every x in E.
3. **Function and evaluation point:** For fixed z, h_z(y)=max{1-<z,y>,0}, embedded in EReal, evaluated at x. The scalar 1 and the zero threshold are fixed constants, not extra parameters.
4. **Admissibility assumptions and branch conditions:** No normalization or nonzero condition is placed on z. Put t=1-<z,x>. The branches are tested in order: t<0; otherwise t=0; otherwise t>0. The last equivalence uses that t is real.
5. **Conclusion and exact quantifier structure:** The full set equality is
   \[
   \partial h_z(x)=
   \begin{cases}
   \{0\},&1-\langle z,x\rangle<0,\\
   \{-\alpha z:\alpha\in[0,1]\},&1-\langle z,x\rangle=0,\\
   \{-z\},&1-\langle z,x\rangle>0.
   \end{cases}
   \]
   Equivalently, for every g in E, the condition
   \[
   \forall y\in E,\ \max\{1-\langle z,x\rangle,0\}
     +\langle g,y-x\rangle\le\max\{1-\langle z,y\rangle,0\}
   \]
   holds if and only if g=0 in the first branch, if and only if there exists a real alpha with 0<=alpha<=1 and g=-(alpha z) in the second branch, and if and only if g=-z in the third branch. Thus every listed vector belongs, and no unlisted vector belongs.
6. **Boundary and degenerate cases:** The equality boundary is <z,x>=1, and its set is the entire closed segment from 0 to -z, including both endpoints alpha=0 and alpha=1. The zero branch corresponds to <z,x>>1; the singleton {-z} branch corresponds to <z,x><1. When z=0, t=1 at every x, so only the third branch occurs and gives {-0}={0}; the function is constantly 1. In particular, the equality and negative branches cannot occur for z=0. When x=0, t=1 for any z, so the set is {-z}. A zero-dimensional ambient space is allowed and necessarily reduces to z=x=0 and the singleton {0}. These are global supporting inequalities, including comparisons with y on the other side of the boundary.
7. **Scope and limitations:** The statement concerns exactly this fixed finite-valued maximum of an affine expression and zero. No label, sample, loss sequence, changing offset, additional penalty, constrained domain, or probabilistic expectation appears. It does not identify any source theorem, establish the hypotheses of an external application, or provide a compiled proof. No claim is made about infinite-dimensional validity, since this header explicitly requires finite-dimensionality.

## Evidence boundary

Only the packet's definitions, ambient typeclass hypotheses, and two unproved statements were read. Their intended set equalities and quantifiers have been reconstructed; mathematical correctness and source fidelity have not been independently established by this decoding exercise.
