# Restricted current-packet reconstruction: S and N01–N03

Only `blind-packet-v1.md` in this run directory was read as mathematical file input this pass. No other file, directory listing, source identity, imported source, proof body, prior verdict, or compilation was accessed. Prior unrelated actor history is not erased; this is restricted current-packet reconstruction, not clean-history blinding. The distinct automated actor is `/root/normal_blind`, requested GPT-6 Astra / medium, without runtime-model attestation or human/external-model review. No source correspondence, proof validation, compilation, chapter certification, or Goal certification is claimed.

Independent SHA-256 of exact raw packet bytes:
`b2cfdb707039e302b15baadf4d8a17f46197594b40755e63f3a6e8879c41d16a`.

N01 and N02 are precise planned terminal types, not asserted here to have compiled bodies. N03 is a retained actual type with no proof supplied. The report preserves this status distinction throughout.

## Supplied context, without imported-definition inspection

The packet supplies D_f={x:f(x)<+∞}, properness P(f) as global exclusion of −∞ together with at least one finite real witness, and C(f) as convexity of the real-height epigraph {(x,r)∈E×ℝ:f(x)≤ι(r)}. These are supplied mathematical context, not independently inspected imported bodies. Write ι for embedding real numbers into EReal.

The supplied intrinsicInterior ℝ A is the image, under inclusion into the ambient space, of the interior of A's preimage in its real affine span. I write ri(A) for exactly this supplied relative-interior notion. It is neither closure(A) nor ambient interior(A). Ambient interior(A), used in N03, uses the whole ambient topology. Membership in either kind of interior entails membership in A under these supplied definitions; the intrinsic version does not demand a full-dimensional domain.

N01 uses a finite-dimensional real normed space E, without an inner-product assumption. N02–N03 use a finite-dimensional real inner-product space F. None of the terminal types explicitly binds CompleteSpace, although finite-dimensional real normed spaces have their usual completeness consequence. The definition of S has a weaker scope: an arbitrary real inner-product space H, without completeness or finite dimension. All these algebraic/normed classes supply zero, so their carriers are nonempty. No measure, probability, temporal information, algorithm, or oracle-input structure appears.

## S — all-ambient-query support relation

1. **Objects/spaces:** A type H with NormedAddCommGroup H and InnerProductSpace ℝ H; an extended-real f:H→EReal; a specified point x∈H; and a subset S_f(x) of candidate vectors g∈H. Neither CompleteSpace nor FiniteDimensional is a binder of this definition.
2. **Quantifiers/information order:** For each f,x and fixed candidate g, test every y∈H. The chosen g must satisfy all queries simultaneously; it is not permitted to vary with y.
3. **Assumptions:** No properness, convexity, finite-value, interior, continuity, or differentiability condition is imposed in the definition.
4. **Conclusion/definition:**
   \[
   S_f(x)=\{g\in H:\forall y\in H,
      f(x)+\iota(\langle g,y-x\rangle)\le f(y)\}.
   \]
   This is global support, not support only against y in D_f or its affine span.
5. **Constants/normalization:** Inner product order g then y−x; coefficient one; non-strict inequality. No nonzero condition, norm normalization, or approximation parameter on g.
6. **Conclusion mode/information:** A deterministic set-valued definition. It does not itself produce a support vector or define a selection rule. If f(x) is finite, each member gives an affine lower support touching at x because the displacement there is zero.
7. **Boundary:** Under standard interpreted EReal arithmetic with finite addends, f(x)=−∞ makes every g pass; an identically-top function also admits every g. Those behaviors are not excluded by S alone. Properness in N02–N03 excludes both problematic regimes via its respective conjuncts. Zero g is allowed when it meets the inequality; uniqueness is not inherent. No empty-ambient-type shortcut is available since the classes provide zero.

## N01 — contact affine support at a specified relative-interior point (planned type)

1. **Objects/spaces:** E with NormedAddCommGroup E, NormedSpace ℝ E, FiniteDimensional ℝ E; extended-real f; specified x∈E; existential continuous real-linear a:E→ℝ and real offset b. No inner product or separate CompleteSpace binder.
2. **Quantifiers/information order:** For every such E,f satisfying global premises, and every specified x∈ri(D_f), there exist a,b which both touch at this x and bound f for every ambient y∈E. The witnesses may depend on f,x but are fixed before the universal y. This is not merely existence of some contact point.
3. **Assumptions:** ∀y∈E, f(y)≠−∞; C(f); x∈intrinsicInterior ℝ D_f. There is no explicit P(f) premise or separately supplied finite witness. Under supplied D and intrinsic-interior semantics, the selected x already belongs to D_f and, with no-bottom, has a finite real value. This explanation does not replace the printed hypotheses with P.
4. **Conclusion:** Proposed exact type
   \[
   \exists a\in\mathcal L(E,\mathbb R)\ \exists b\in\mathbb R:\quad
   \iota(a(x)+b)=f(x)\ \land\
   \forall y\in E,\ \iota(a(y)+b)\le f(y).
   \]
   The affine minorant is required to touch f at the prescribed relative-interior point; a global lower bound without the equality would be a weaker conclusion.
5. **Constants/normalization:** Unit coefficients, exact contact, and non-strict global inequality. No norm bound, strict gap, nonzero slope, uniqueness, or specified offset value.
6. **Conclusion mode/information:** Deterministic existence proposition, explicitly planned. No compiled body or proof is supplied by its presentation. No differentiability or gradient construction is assumed; a is a continuous functional on the whole E, not merely on the affine span.
7. **Boundary:** Lower-dimensional domains and domains with empty ambient interior are not excluded if x lies in the supplied intrinsic interior. No closedness, lower semicontinuity, full-dimensionality, or loss differentiability premise is present. +∞ is allowed away from the finite domain; −∞ is excluded globally. Empty D_f has no admissible x. A singleton finite domain can have relative interior even without ambient interior. The output a may be zero, and contact is not asserted at arbitrary domain boundary points lacking the stated relative-interior membership.

## N02 — support-vector existence at a relative-interior point (planned type)

1. **Objects/spaces:** F with NormedAddCommGroup F, InnerProductSpace ℝ F, FiniteDimensional ℝ F; f:F→EReal; properness P(f), epigraph convexity C(f), specified x∈F, and S_f(x)⊆F. No explicit CompleteSpace binder.
2. **Quantifiers/information order:** For every proper convex-epigraph f and every x∈ri(D_f), some g∈F exists that satisfies the support inequality for every y∈F. Expanded conclusion has ∃g before ∀y; no one vector is required to work at every x simultaneously.
3. **Assumptions:** P(f), including global no-bottom and a finite witness; C(f); and intrinsic-interior membership of the specified x. No assumed support existence, gradient, or differentiability is an input.
4. **Conclusion:** Proposed nonemptiness of S_f(x), namely
   \[
   \exists g\in F\ \forall y\in F,\quad
   f(x)+\iota(\langle g,y-x\rangle)\le f(y).
   \]
   Properness and x∈D_f make the base value finite under supplied semantics, so this is touching affine support at x expressed through a vector rather than a free offset b.
5. **Constants/normalization:** Coefficient one and displacement y−x. The effective affine offset is anchored by f(x); no arbitrary lowering of the affine function may replace this contact form. No nonzero or unit-norm condition on g.
6. **Conclusion mode/information:** Deterministic existential result as a planned type expression. It does not define a computable, measurable, or unique selector. It is stronger than merely asserting some unattached global affine minorant. No proof or compilation acceptance is inferred.
7. **Boundary:** Relative interior can be nonempty for a lower-dimensional or singleton domain; full-dimensionality is not required. All ambient y, including points outside D_f, are tested. No closure or differentiability hypothesis. At y outside D_f, the supplied domain/no-bottom context gives top values and the comparison is compatible with them; no bottom values are permitted. The claim gives no support-existence assertion at every point of D_f or at arbitrary relative-boundary points. Zero g is permitted; uniqueness is absent.

## N03 — support-vector existence at an ambient-interior point (retained type)

1. **Objects/spaces:** The same finite-dimensional real inner-product setting as N02, extended-real f, point x, and support set S_f(x). Completeness is not a separate printed binder.
2. **Quantifiers/information order:** For every f satisfying P and C, and every specified x∈interior(D_f) in the ambient space F, there exists one g supporting f against every y∈F.
3. **Assumptions:** P(f); C(f); x∈ambient interior(D_f). This header uses ordinary interior, not the affine-span intrinsic interior used in N01–N02. No differentiability, closedness, or explicit support-existence premise is supplied.
4. **Conclusion:**
   \[
   S_f(x)\ne\varnothing,
   \quad\text{equivalently }\exists g\in F\ \forall y\in F,
   \ f(x)+\iota(\langle g,y-x\rangle)\le f(y).
   \]
   The support is anchored at x and global in its query y.
5. **Constants/normalization:** Exact support inequality with coefficient one, no error or gradient-norm bound, and no nonzero/uniqueness demand.
6. **Conclusion mode/information:** Retained actual type with no proof supplied. This report does not compile or independently validate it. No algorithm, probability, or causal oracle property follows from set nonemptiness.
7. **Boundary:** A domain with empty ambient interior offers no applicable x, even if it has relative-interior points covered by the separate planned N02 type. No full-dimensionality assumption is separately written; the pointwise ambient-interior premise itself restricts applicability. Empty domain is already incompatible with properness under supplied semantics. +∞ outside D_f is allowed and global no-bottom remains explicit through P. The conclusion does not certify support at all feasible/domain points or uniqueness of the supporting vector.

## Interpretation limits

The displayed S definition and three exact terminal types were read from this packet. D/P/C and intrinsicInterior are reconstructed only from the supplied imported context, not independently inspected source bodies. The key distinctions are contact at the prescribed point versus mere minorant existence, normed-space functional witnesses versus inner-product vector witnesses, relative versus ambient interior, global query range, and planned N01/N02 versus retained N03 status. No source matching, proof, compiled-public, or Goal acceptance follows.
