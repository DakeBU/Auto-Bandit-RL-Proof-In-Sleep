# Fresh source-blind reconstruction

The header states quadratic growth at an already attained minimum on a convex subset of a real normed vector space:

`f(p) + (lam/2) * ||q-p||^2 <= f(q)`, with both function values interpreted as finite real values.

- E : Type* is arbitrary; NormedAddCommGroup E supplies an additive commutative group with a genuine norm, and NormedSpace R E makes E a real normed vector space.
- f : E -> EReal is an extended-real-valued function on all E.
- V : Set E is the comparison set.
- lam : R is the curvature parameter.
- hf : SourceProper f says f x != bottom for every x in E, and there exist x in E and real r with f x = (r : EReal). It is global properness and has no extra topology binder.
- hV : Convex R V says V contains every convex combination of its members.
- hdom : V subset effectiveDomain f says f x < top for each x in V; effectiveDomain itself does not exclude bottom, but hf excludes it.
- hlam : 0 <= lam permits zero curvature.
- hstrong universally quantifies x in V, y in V and real a with 0 < a < 1, and bounds f(a*x+(1-a)*y) by a*f x+(1-a)*f y minus the real quantity (lam/2)*a*(1-a)*norm(x-y)^2 embedded in EReal.
- p : E is a supplied point; hp : p in V ensures membership.
- hmin : IsMinOn f V p means f p <= f x for every x in V. IsMinOn does not itself require p in V; hp supplies it.
- q : E is an arbitrary comparison point; hq : q in V restricts comparison to V.

All values on V are neither bottom nor top by hf and hdom. Convexity puts every interpolated point in V, so hstrong also compares finite values. EReal.toReal maps either infinity to zero and a finite embedded real to itself; its infinity branches cannot occur for p, q, or these interpolated points.

The strong-convexity inequality uses EReal order, EReal multiplication/addition/subtraction and real-to-EReal coercions. The curvature expression is first computed entirely in R and then embedded. a and 1-a are strictly positive; lambda is nonnegative. No infinity arithmetic is needed on the stated domain.

This is conditional growth at an attained global minimum relative to V. It neither proves existence nor asserts minimization outside V. hp makes V nonempty; q is also supplied with membership.

No hypothesis contains the desired quadratic gap. hmin supplies ordinary minimum ordering, without the quadratic gap. hstrong supplies the interpolation bound. No hypothesis literally postulates the requested quadratic-growth bound. When lam = 0 the conclusion reduces to the assumed minimum ordering after finite-value conversion. Real normed vector space, convex V, V contained in finite domain under global properness, lam >= 0, interpolation inequality on all pairs in V, and an attained minimizer. Global properness is stronger than merely requiring finiteness on V and forbids bottom even outside V. The theorem does not assume completeness, finite dimension, inner product, differentiability, continuity, closedness, compactness, or strict positivity of lam. No additional hidden restriction found in inspected definitions. Whether visible restrictions are supported by an external source cannot be determined in a source-blind review. No empty-set application is possible because hp requires p in V. Singleton V and lam=0 are allowed degeneracies, not infinity totalization. toReal infinity totalization is blocked by explicit hypotheses.

Requested model: GPT-6 Astra, medium. Runtime attestation is unavailable.

Permitted exposure: Neutral complete header, exact imported definitions SourceProper/effectiveDomain/IsMinOn/EReal.toReal and standard classes as necessary.

No paper, source proposals, topology packets, reviews, candidate theorem BODY, or history read. No proof search.

Incidental exposure: A targeted SourceProper search returned OnlineClosedProper line 10 documentation ('SourceProper itself has no topology binder; the ACTUAL proper-indicator iff') and line 80 proper-indicator theorem signature. A short definition window also showed SourceClosed definition, TopologicalSpace section context and a following theorem signature. EReal.toReal window included two preceding proof-tail lines from an unrelated library lemma. These are logged rather than represented as zero incidental exposure. None informed source-equivalence judgment.

## Read manifest

- E:/ABRL/worktrees/research-online-book/tmp/online-ch2-b4-next-strong-convex-header-20261011/neutral-complete-header-v1.txt
  - SHA256: ded5adebef211f810552abbc4eced856dd9fff59f268989e9c1ff5a4ecd3d590
  - Read scope: Full neutral header
- E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineClosedProper.lean
  - SHA256: c66f00c33b45fb8a0e11583eeadf506e176c16166ce2af02f41f0674507cebe7
  - Read scope: Targeted SourceProper/import matches; lines 1 and 26-35
- E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineConvexExtended.lean
  - SHA256: bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a
  - Read scope: effectiveDomain definition line 24
- E:/ABRL/worktrees/research-online-book/.lake/packages/mathlib/Mathlib/Order/Filter/Extr.lean
  - SHA256: 02b73ed141a3bc3e38da7a237f369cbdf8aad80dfa155572cc13e588334a4679
  - Read scope: IsMinOn definition match; lines 94-100 and 101-112
- E:/ABRL/worktrees/research-online-book/.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean
  - SHA256: bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922
  - Read scope: toReal definition match; lines 207-217

Only these create-only tmp artifacts were written. No canonical source edits, Lean build, proof search, or source-equivalence assessment.

