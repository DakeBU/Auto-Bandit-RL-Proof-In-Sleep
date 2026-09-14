Leaf01: native-fenced definition2.2 uses mathlib convex_iff_forall_pos; domain convexity uses epigraph points at real upper bounds of every non-top value (including bottom); indicator-domain identity splits membership. No broader terminal is declared without a proof.

Leaf01 failed because the frozen binder lambda is a parser keyword. v1 stabilization is retracted for ill-formed target syntax. v2 is alpha-renaming only (theta), with new native fingerprints and retained old v1 evidence. Domain/indicator-domain proofs showed no errors.

V2 type probe has exactly seven deliberate unproved-body errors and no other errors; this is header elaboration evidence, not compiled proof evidence. Leaf02 passes the first three proofs. Leaf03 implements indicator epigraph/product equivalence and the exact noBot-toReal epigraph bridge, then reuses the real-valued mathlib epigraph equivalence.

Leaf03: indicator/product and finite epigraph identity elaborate; the generic mathlib equivalence leaves scalar/domain metavariables unresolved. Leaf04 supplies explicit real scalar, domain and finite-part function arguments, without changing a statement.

Leaf04 passes six helpers. Terminal01 explicitly proves finite EReal/coerced-real Jensen equivalence using domain convexity and noBot for all three evaluated points, then applies mathlib convexOn_iff_forall_pos. The source strict theta interval is preserved in both directions. PR117 remote main CI34810996453 completed success; PR118 mainCI remains running.

Public canary01 failed: simp already solved one proof before a redundant le_rfl; the numeral2 coercion was ambiguous; an unparenthesized fractional smul parsed incorrectly in the test expression. Canary02 uses explicit real scalars and embedded real2, removes the redundant tactic. Failed-canary axiom output containing elaboration recovery sorryAx is not acceptance evidence; no sorry/admission appears in source, and successful fresh canary axioms remain required.

Canary02 leaves a normalized-membership issue: hx/hy are stated as membership in Ici, so if_pos does not rewrite the literal real inequality. The previous redundant-tactic diagnosis was incomplete. Canary03 explicitly changes hx/hy to real inequalities. The added noBot indicator-addition header probe has exactly one deliberate unproved-body error; its body uses an exact epigraph intersection and the locally checked EReal.add_top_of_ne_bot API.

Canary03 now normalizes the inequality to reflexivity; simp only deliberately does not include le_refl. Canary04 closes it with le_rfl after that normalization. Source/counterexample re-audit found no missing hypotheses; previous errors were elaboration of the concrete test. Added an active indicator constraint and the empty-domain Theorem2.4 instance before final canary verification.

Public canary04 passes with only standard axioms. Site01 rejected missing highlight metadata for the new route; site02 supplies four source-qualified theorem highlights, preserving the single underlying declaration registry. No generator limit or validation was bypassed.
