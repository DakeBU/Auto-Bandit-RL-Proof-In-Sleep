# Restricted-input reconstruction of Q0, Q1, M01, M02

This fresh pass read only `blind-packet-v1.md` in this directory as mathematical file input. No other source, public-name map, proof, prior verdict, or file was consulted. Earlier unrelated actor history is not erased or claimed absent. The actor is a distinct automated decoder, requested GPT-6 Astra / medium; this is not an attestation of the runtime model. No human or external-model review, compilation, proof validation, source acceptance, or chapter/Goal certification is claimed.

Independently calculated SHA-256 of the packet's exact raw bytes:
`51a3171cc6b78563367bbf56e6175e781f21b64f699f141900221a5aced657db`.

Throughout, E is an arbitrary type, not necessarily inhabited, and has no algebraic, topological, or convex structure. Write ι(r) for the EReal embedding of a real number r, top for +∞, bottom for −∞, D_f=Q0(f), and I_V=Q1(V). EReal order, addition, and embeddings are imported but not defined in the packet. Their usual mathematical meanings below are interpretations, not verified library code. In particular the packet does not expand the mixed-infinity addition convention. The conclusions must retain their exact finite-witness and no-bottom distinctions without silently replacing formal addition with an unrelated extended-arithmetic convention.

## Q0 — below-top domain

1. **Objects:** A type E, function f:E→EReal, and a subset D_f of E.
2. **Quantifiers:** The definition is available for every E and f; its membership condition applies to every x∈E.
3. **Assumptions:** None on f. In particular no exclusion of bottom and no finite-value witness is required.
4. **Conclusion:**
   \[
   D_f=\{x\in E:f(x)<+\infty\}.
   \]
5. **Normalization:** The inequality is strict at top. This is a domain defined by order, not by toReal or by an existential real equality.
6. **Information/probability:** Deterministic set definition with no randomness or information-order condition.
7. **Boundary:** Under the usual EReal order interpretation, a finite value and −∞ both satisfy the membership test, while +∞ does not. Thus D_f is not generally the finite-real-valued locus. It can be empty; when E is empty there are no members or pointwise instances.

## Q1 — extended indicator

1. **Objects:** Arbitrary E, subset V⊆E, and extended-real function I_V.
2. **Quantifiers:** Every V and every x∈E.
3. **Assumptions:** No nonemptiness, convexity, or other condition on V.
4. **Conclusion:**
   \[
   I_V(x)=\begin{cases}0,&x\in V,\\+\infty,&x\notin V.\end{cases}
   \]
5. **Normalization:** Zero inside, top outside. This is not a real-valued 0/1 indicator.
6. **Information/probability:** Deterministic classical membership case distinction; no computational membership oracle is certified.
7. **Boundary:** V=∅ gives the constant-top function; V=E gives constant zero. The function never takes bottom. An empty E gives the unique function from the empty type.

## M01 — exact finite-real locus of the indicated sum

1. **Objects:** Arbitrary E, f:E→EReal, V⊆E, point x∈E, and formal EReal sum f(x)+I_V(x).
2. **Quantifiers:** For every E,f,V,x, an equivalence holds between two propositions. On the left a real witness exists for the sum; on the right membership in V is conjoined with existence of a real witness for f(x). The two occurrences of the existential variable r are independently scoped.
3. **Assumptions:** None beyond the types. Crucially, there is no hypothesis that f avoids bottom, no nonempty-set hypothesis, and no global finite-value condition.
4. **Conclusion:**
   \[
   \big(\exists r\in\mathbb R:\ f(x)+I_V(x)=\iota(r)\big)
   \iff
   \big(x\in V\ \land\ \exists s\in\mathbb R:\ f(x)=\iota(s)\big).
   \]
   In words, adding this indicator yields a finite real value exactly at points inside V where f itself has a finite real value. This is an equivalence of existence statements, not an asserted equality of selected witnesses.
5. **Normalization:** The indicator's finite contribution is zero; the other branch is top. Addition is ordinary imported EReal addition. The test is equality to an embedded real, not a below-top test and not a conversion to real.
6. **Information/probability:** Deterministic pointwise characterization, with no algorithm, probability, or observation restriction.
7. **Boundary:** Inside V, either infinity for f(x) fails the finite-witness condition. Outside V, the right side is false regardless of f(x), so the supplied header asserts that the left side has no finite-real witness even when f(x)=−∞ and the sum involves both infinities. It does not state the exact value of that mixed-infinity sum. If V=∅, both sides are false at each x; if V=E, it characterizes f(x)+0. For empty E there is no x to instantiate. These cases do not justify adding an unwritten no-bottom premise.

## M02 — below-top domain after adding the indicator

1. **Objects:** Arbitrary E, f:E→EReal, subset V, and the below-top domains of f and x↦f(x)+I_V(x).
2. **Quantifiers:** For every E and f, assuming a global no-bottom property, and for every V, an equality of sets holds. Pointwise it means the corresponding membership equivalence for every x.
3. **Assumptions:**
   \[
   \forall x\in E,\quad f(x)\ne-\infty.
   \]
   This premise is global, including points outside V. No assumption that f is finite somewhere, that V is nonempty, or that V intersects D_f is supplied.
4. **Conclusion:**
   \[
   D_{\,x\mapsto f(x)+I_V(x)}=D_f\cap V.
   \]
   Equivalently, the sum is below top exactly when x∈V and f(x)<top. Under the stated no-bottom premise, below-top values of f are finite in the usual EReal interpretation.
5. **Normalization:** Set intersection rather than union; strict order cutoff at top on both domains; ordinary EReal addition with the 0/top indicator.
6. **Information/probability:** Deterministic set identity. Unlike M01, it controls an order-defined domain, so its explicit no-bottom premise must be retained.
7. **Boundary:** f≡+∞ is allowed and both sides are empty. V=∅ also yields empty sets under the premise; V=E reduces to the domain of f+0. If E=∅, the premise is vacuous and both sets are empty. Bottom-valued f are outside the theorem's assumptions: M01's finite-witness equivalence cannot by itself justify the same below-top identity in their presence. The mixed-infinity arithmetic that would govern such excluded cases is imported and not specified by this packet; no counterexample value or stronger theorem is certified here.

## Distinction preserved

The finite-real locus \(\{x:\exists r\in\mathbb R,\ f(x)=\iota(r)\}\) excludes both infinities, whereas Q0's below-top locus includes bottom under the usual EReal order. M01 needs no no-bottom hypothesis because its predicate is finite-real witness existence. M02 explicitly excludes bottom everywhere and concludes an equality of below-top domains. No proof or source verification was performed for either header; imported conventions remain interpretations unless fixed by the supplied definitions or statements.
