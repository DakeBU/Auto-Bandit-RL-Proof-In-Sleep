# Support-growth neutral-header reconstruction

Actor: `/root/b4_finite_identity_blind`. Requested model/effort: GPT-6 Astra / medium; actual runtime settings were not independently attested.

The sole input read in this task was `E:/ABRL/worktrees/research-online-book/tmp/online-b4-support-neutral-20261011/header-v1.txt`. Raw SHA256: `23e26732b827730a343a1dd758a19a39d4f8d4af06941330f9636272d3114d57`, matching the assignment. One raw-byte read supplied both hashing and text display.

## Exposure disclosure

I previously read the finite-regret-identity neutral header at `tmp/online-ch2-b4-finite-identity-proposal-20261011/neutral-proposed-header-v1.txt`, SHA256 `92e0dcfac53595e35b68bfd8083c09640d06da809355ab02ec4eb4b007b0bd67`, and produced its semantic analysis. No source book or proof BODY was opened in that task. Generic inherited instructions, skill catalog, ABRL workspace instructions, environment metadata, supplied memory-summary context, prior analysis, and the current assignment remain visible. I also have general mathematical familiarity with strong convexity and affine supports. This is not a claim of zero background or of never encountering the book. No additional book-specific source knowledge was consulted or used here.

No source book, proposal, author BODY, production module BODY, imported module, other review report, or memory file was opened for this task. The only imports visible in the header were `BanditRLProof.OnlineStrongConvexMinimum` and `Mathlib.Analysis.Normed.Operator.Basic`.

## Exact mathematical assertion

For every real normed vector space E, extended-real-valued function f, set V, and real parameter lam, assume:

- `SourceProper f`, a named imported predicate whose definition is not displayed.
- V is convex and is a subset of `effectiveDomain f`, another imported object whose definition is not displayed.
- lam is nonnegative.
- For all x,y in V and real 0<a<1,

```text
f(a*x+(1-a)*y)
  <= a*f(x)+(1-a)*f(y)
     - coerce((lam/2)*a*(1-a)*norm(x-y)^2).
```

The argument uses vector scalar multiplication. The right-side values, products, subtraction, and inequality are in EReal, with real quantities coerced as displayed in the original header.

For every p in V, every supplied continuous real-linear functional `g : E ->L[Real] Real` satisfying

```text
f(p) + coerce(g(z-p)) <= f(z)    for all z in V,
```

and every q in V, the theorem asserts the real inequality

```text
toReal(f(p)) + g(q-p) + (lam/2)*norm(q-p)^2 <= toReal(f(q)).
```

E is an implicit universe-polymorphic type parameter, with normed additive commutative group and real normed space instances. The named ordinary binders are explicit. Neither completeness nor finite dimension is required. There is no openness, closedness, compactness, boundedness, interior, differentiability, or smoothness assumption in the visible header.

## Finiteness boundary

**The two custom imported definitions cannot be reconstructed exactly from this header alone.** Their names suggest conventional properness and effective-domain conditions, but the allowed read does not certify which infinities they exclude or any existence clause in properness.

Standard EReal semantics gives `toReal(coerce(r))=r` for finite real r; both infinities convert to zero. Therefore conversion by itself is not a valid general order-preserving passage from extended reals to real numbers.

Conditionally, if `SourceProper` excludes negative infinity everywhere and `effectiveDomain` excludes positive infinity, or if the effective domain itself consists of finite-valued points, the assumptions ensure finiteness throughout V. The conclusion then has the usual reading

```text
f(q) >= f(p) + g(q-p) + (lam/2)*norm(q-p)^2.
```

An authorized definition-aware review still needs to confirm those expansions and finiteness at p, q, and intermediate convex combinations. Convexity puts those combinations in V. This is an inspection boundary, not evidence that the actual definitions are deficient.

## Constants, support, and scope

The improvement has exactly coefficient lam/2 and squared norm of q-p. The interpolation correction is exactly `(lam/2)*a*(1-a)` times squared norm of x-y. The linear term uses q-p; reversing it would change its sign. The norm orientation alone is immaterial. The interpolation coefficient ranges over the open unit interval; lam=0 is allowed.

The theorem strengthens a **given** support on V. It does not produce a support, select g, prove support existence at arbitrary p, or assert support outside V. It does not assert attainment of an infimum, existence or uniqueness of minimizers, an algorithm, or any algorithmic performance bound. If g=0 is separately available with its support hypothesis, the conclusion conditionally becomes quadratic growth from p; the header does not supply that instance.

Empty V admits no p or q satisfying their membership binders. Absence of an admissible support similarly makes the implication unusable at that point. For q=p the conclusion is reflexive because g(0)=0 and the norm term vanishes. Singleton V therefore carries no nontrivial growth content. The interpolation range is not empty: a=1/2 is available. Infinity-related vacuity cannot be independently ruled out until the custom definitions are inspected.

No proof BODY is present. This report accepts neither a proof nor source-faithfulness and reports no compilation. No Lean/build/Git command, tracked change, freeze-state change, or Goal-state change was performed. Outputs are create-only UTF8 without BOM, LF, in the assignment-designated ignored temporary directory; ignore status was not independently inspected under the restricted read scope.
