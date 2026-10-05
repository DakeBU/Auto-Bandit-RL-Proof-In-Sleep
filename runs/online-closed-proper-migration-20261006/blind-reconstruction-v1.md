# Restricted current-packet reconstruction: C, P, N01–N03

This pass read only `blind-packet-v1.md` in this directory as mathematical file input. No directory listing, source, imported proof body, prior verdict, other file, or compilation was used. Prior unrelated actor history is not erased: this is restricted current-packet reconstruction, not clean-history blinding. The actor is `/root/normal_blind`, requested GPT-6 Astra / medium, without runtime-model attestation or human/external-model review. No source matching, proof validation, compilation, chapter certification, or Goal certification is claimed.

Independent SHA-256 of the exact raw packet bytes:
`57b4976077e542841f6564a229b1072c7a0d8dd1953ad019803b1e6f6189bf3b`.

## Context and inspection boundary

The packet fully supplies the definitions C and P; these displayed definitions were read. Its supplied notation describes I_V(x) as 0 for x∈V and +∞ otherwise. The original imported indicator body was not inspected. EReal has bottom −∞, embedded real values ι(r), and top +∞, as supplied. Standard topology and LowerSemicontinuous notation are interpreted mathematically, not checked against imported implementation.

The neutralized actual types distinguish their binders. C requires TopologicalSpace E; P itself has no topological class binder. Nevertheless N03 retains TopologicalSpace E in its supplied actual theorem type, and this reconstruction does not erase it. No metric, vector-space, convexity, separation, compactness, completeness, or finite-dimensional assumption occurs.

## C — closed finite-height sublevel sets

1. **Objects/spaces:** A topological space E and extended-real function f:E→EReal.
2. **Quantifiers/information order:** For every f, the property universally quantifies over every finite real level r. There is no probabilistic or temporal order.
3. **Assumptions:** Only TopologicalSpace E. No properness, convexity, finite witness, or no-bottom condition.
4. **Definition/conclusion:**
   \[
   C(f)\iff\forall r\in\mathbb R,\quad\{x\in E:f(x)\le\iota(r)\}\text{ is closed in }E.
   \]
5. **Constants/normalization:** Non-strict sublevel inequality; quantification over real thresholds only, not an additional quantifier over EReal levels.
6. **Conclusion mode:** Exact supplied predicate definition, not a statement that f is finite-valued or that its effective domain is closed.
7. **Boundary:** Bottom-valued points belong to every finite sublevel set; top-valued points belong to none. The constant +∞ function has all these sublevels empty, and constant −∞ has all equal E, so both satisfy C under standard set topology. Empty E is allowed. No restriction requiring closedness of the below-top domain is built into C.

## P — properness

1. **Objects/spaces:** An arbitrary type E and f:E→EReal. The actual definition signature of P has no TopologicalSpace binder.
2. **Quantifiers/information order:** A conjunction of a global universal exclusion and an existential finite witness: first ∀x, then ∃x∃r∈ℝ. The existential point need not have any distinguished location.
3. **Assumptions:** None beyond the function type; no topology or convexity in the definition.
4. **Definition/conclusion:**
   \[
   P(f)\iff(\forall x\in E,\ f(x)\ne-\infty)
       \ \land\ (\exists x\in E\ \exists r\in\mathbb R,\ f(x)=\iota(r)).
   \]
5. **Constants/normalization:** At least one finite embedded real value, not merely a point below top when bottom has not yet been excluded. No prescribed value, bound, or normalization for r.
6. **Conclusion mode:** Exact supplied predicate definition; it is independent of C and has no probability content.
7. **Boundary:** +∞ values are permitted away from the finite witness. Constant +∞ fails the witness condition, and any bottom value fails the global condition. When E is empty, the universal part is vacuous but the existential part fails, so P is false. Properness does not require global finiteness or attainment of a minimum.

## N01 — equivalence with lower semicontinuity

1. **Objects/spaces:** Arbitrary topological E and extended-real f, with C from its supplied definition and imported LowerSemicontinuous.
2. **Quantifiers/information order:** For every such E and every f, the equivalence holds. There is no sequence, probability, or algorithmic information condition.
3. **Assumptions:** TopologicalSpace E only. No no-bottom, finite witness, convexity, or separation axiom.
4. **Conclusion:**
   \[
   \big[\forall r\in\mathbb R,\ \{x:f(x)\le\iota(r)\}\text{ closed}\big]
      \iff\operatorname{LowerSemicontinuous}(f).
   \]
   In standard topological language this identifies closed finite sublevel sets with lower semicontinuity of the extended-real function.
5. **Constants/normalization:** Real thresholds and non-strict sublevels exactly as in C. It is not an upper-semicontinuity assertion or a continuity equivalence.
6. **Conclusion mode:** Two-way predicate equivalence for each f. The imported LowerSemicontinuous definition was not inspected; no implementation-level proof is supplied by this decoding.
7. **Boundary:** Both infinities remain in scope. Constant ±∞ and empty-domain cases are not excluded. In a general topological space this should not be weakened to only a sequential criterion without extra topological hypotheses. The result does not assert properness, closedness of the finite-valued domain, or any attainment property.

## N02 — closedness of the indicator in terms of its set

1. **Objects/spaces:** A topological E, arbitrary subset V⊆E, and the supplied 0/+∞ indicator I_V.
2. **Quantifiers/information order:** Every V in every such topological E. No choice of witness point or finite level precedes the statement; C already universally quantifies levels.
3. **Assumptions:** TopologicalSpace E only; V need not be nonempty or convex.
4. **Conclusion:**
   \[C(I_V)\iff V\text{ is closed}.\]
   Thus the indicator has closed finite-height sublevel sets exactly when its set is closed.
5. **Constants/normalization:** Indicator zero inside and +∞ outside. Under supplied notation, finite sublevels are empty for r<0 and V for r≥0; this explains the exact zero threshold without a different indicator convention.
6. **Conclusion mode:** Deterministic equivalence, not a claim that every indicator or every subset is closed. No probabilistic condition.
7. **Boundary:** V=∅ is included: I_V is constant +∞ and C holds, matching closedness of ∅. V=E gives constant zero and also qualifies. No properness or nonempty-set conclusion follows from C(I_V). Nonclosed V simply fails the equivalent conditions.

## N03 — properness of the indicator in terms of nonemptiness

1. **Objects/spaces:** A topological E as retained in the supplied actual N03 type, subset V, and indicator I_V. P itself remains a topology-free definition.
2. **Quantifiers/information order:** Every such E and V. The right side is ∃x∈E, x∈V; the left includes the finite-real witness specified in P.
3. **Assumptions:** Only the theorem's TopologicalSpace binder. No closedness, convexity, boundedness, or nonemptiness is a premise.
4. **Conclusion:**
   \[P(I_V)\iff V\ne\varnothing\quad\text{(that is, }\exists x\in V\text{)}.\]
   The indicator is proper exactly when there is a point inside its set, where its value is the finite real zero; it never takes bottom by the supplied indicator convention.
5. **Constants/normalization:** The available finite witness value is exactly 0. Outside V the value is top, which cannot be an embedded finite real witness.
6. **Conclusion mode:** Deterministic equivalence. It is not a proof of C(I_V) or of closedness of V, and has no probability component.
7. **Boundary:** V=∅ fails properness even though N02's closedness property holds. If E is empty all its subsets are empty, and both sides are false. A nonempty nonclosed V still satisfies this properness equivalence. The topological binder is present in this theorem even though the described set-theoretic property does not need topology mathematically; the reconstruction retains it rather than silently strengthening the actual type.

## Limits

All five items receive seven-slot coverage. C and P are reconstructed from their fully displayed definitions, while indicator and LowerSemicontinuous semantics are limited to supplied notation and standard interpretation. Closed finite-height sublevels and existence of a finite witness are distinct properties; neither has been substituted for the other. No proof, source correspondence, compiled declaration, or broader Goal acceptance is certified.
