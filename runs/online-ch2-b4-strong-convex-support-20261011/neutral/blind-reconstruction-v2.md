# Support-growth neutral reconstruction V2

Actor: `/root/b4_finite_identity_blind`. Requested model/effort: GPT-6 Astra / medium; runtime settings are not independently attested. V1 is preserved unchanged.

## New evidence and exposure

The only file newly read was `imported-definitions-v1.txt` in this report directory. Its raw SHA256 is `d387956be74876b77456c22f6fe444810681515bd0e6ec3111a83716271cae45`, matching the supplied digest. One byte read supplied hashing and text display.

The original support header remains in context at previously verified SHA256 `23e26732b827730a343a1dd758a19a39d4f8d4af06941330f9636272d3114d57`; it was not reread. My earlier exposure to the finite-identity header (SHA256 `92e0dcfac53595e35b68bfd8083c09640d06da809355ab02ec4eb4b007b0bd67`) and its semantic analysis also remains. Generic inherited instructions, skill catalog, workspace instructions, environment metadata, memory-summary context, and assignments were already visible. I have general mathematical knowledge of convexity and supports. This is not a zero-background claim or a claim of never having encountered the book.

The new text exposes exactly two definition bodies and their typing context. No theorem proof BODY, source book, proposal, production module BODY, other review report, memory file, or Git state was read. The supplied text's claimed production provenance was not independently audited.

## The finiteness boundary is resolved

The actual supplied definitions say:

```text
SourceProper f :=
  (for all x, f(x) != bottom)
  and (there exist x and real r with f(x)=coerce(r))

effectiveDomain f := {x | f(x) < top}
```

`SourceProper` has a topological-space typing context but its displayed definition imposes no continuity or semicontinuity. The effective-domain definition has additive-group and real-module typing context; its set membership excludes positive infinity, while allowing negative infinity in isolation.

For **every v in the original literal V**, hdom now gives `f(v)<top` and hf gives `f(v)!=bottom`. Thus f(v) is finite. No intersection, restriction, closure, or replacement of V is needed. The finite witness in the second properness conjunct may be outside V; finiteness on V follows from the first conjunct plus hdom. hp and hq independently ensure that an actual instance has nonempty V.

Consequently f(p) and f(q) are finite. These endpoints are the only `toReal` occurrences in the conclusion, and their conversion gives the actual finite real values. The fallback value zero for EReal infinities is irrelevant there. All z in the support hypothesis are also finite-valued. Convexity puts the intermediate combinations in V and hence makes their values finite too; this observation does not specify a proof strategy or require intermediate `toReal` calls.

Outside V, f may still be positive infinity. It is never negative infinity anywhere under hf.

## Reconstructed assertion and exact quantifiers

For an arbitrary real normed vector space E, an extended-real-valued f, a convex V contained in its effective domain, and real lam>=0, assume the stated properness and, for every x,y in V and real 0<a<1,

```text
f(a*x+(1-a)*y)
  <= a*f(x)+(1-a)*f(y)
     - coerce((lam/2)*a*(1-a)*norm(x-y)^2).
```

Given any p in V and any continuous real-linear functional g satisfying, for **every z in V**,

```text
f(p)+coerce(g(z-p)) <= f(z),
```

the assertion is, for every q in V,

```text
toReal(f(p)) + g(q-p) + (lam/2)*norm(q-p)^2 <= toReal(f(q)).
```

E is implicit and universe-polymorphic, with normed additive commutative group and real normed space instances. Named ordinary binders are explicit. Completeness and finite dimension are not assumed. The single g satisfies support simultaneously for all z in V; it is not selected anew for each comparison point. The coefficient is exactly lam/2, the support direction is q-p, and lam=0 is permitted. The interpolation coefficient is quantified over the open unit interval.

Writing F(v)=toReal(f(v)) on V, the now-verified finite-value semantics makes the support hypothesis exactly `F(p)+g(z-p)<=F(z)` for every z in V. The conclusion strengthens that same support to `F(q)>=F(p)+g(q-p)+(lam/2)*norm(q-p)^2`.

## Boundaries retained

This strengthens a given support; it neither constructs a support nor ensures one exists at any chosen p. Support is on V only. There is no attainment, optimizer existence or uniqueness, algorithm, regret, convergence, or performance statement. A separate g=0 support instance would yield quadratic growth from p on V, but the theorem does not supply such an instance.

Empty V has no hp/hq instance. A point without an admissible supporting g yields no application. q=p is reflexive because g(0)=0; singleton V has no nontrivial growth content. lam=0 reduces the conclusion to the real support inequality. Infinity-based vacuity on V is now ruled out by the actual definitions.

No proof BODY has been seen and no compilation was performed. V2 resolves the imported-definition/finite-value question, not proof correctness, kernel acceptance, source-faithfulness, source attribution, or correspondence of the supplied definition text to a specific production commit. No clean-worktree condition was imposed. No tracked file, freeze state, or Goal state was changed. Only create-only V2 files were written in the assignment-designated ignored directory, as UTF8 without BOM and LF newlines; ignore status was not independently inspected.
