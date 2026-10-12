# Blind header reconstruction: bottom_singleton_attains

Only the two authorized input files in this packet were used. No source, import, proof, review, or Lean execution was consulted. This reconstruction does not certify proof validity, compilation, source acceptance, or use of any provider theorem.

Verified input SHA256:

- declaration-v1.txt: e0137f3c40f640254fcb7bbcac5ed7f9ca7fb64912683e4b8fa02cc698ae4f00
- definition-context-v1.txt: f2d6064cf8f3156642a6ba558a6d557338029159fad2d6f3f3f43037b6e9ae94

## Definitions and binders

The ambient domain is ℝ with its ordinary topology. The function objective : ℝ → EReal is constant bottom, where bottom is negative infinity. The feasible set is the singleton {0}. The effective domain is {x | objective(x)<top}, where top is positive infinity. Hence its effective domain is all of ℝ, including every bottom-valued point.

There are no external theorem parameters, instance binders, or hypothesis arrows in the supplied header. The theorem asserts a closed conjunction of six propositions. Its only explicit bound variable in the header is the existential p inside the first conjunct; its inferred type is ℝ. Expanding IsMinOn introduces a universal real comparator q. Expanding SourceProper introduces universal x:ℝ and, separately, existential x:ℝ and r:ℝ.

## Exact conjunction order

1. There exists p:ℝ such that p∈feasible and IsMinOn objective feasible p. Fully expanded: ∃ p:ℝ, p∈{0} ∧ ∀ q:ℝ, q∈{0} → objective(p)≤objective(q).
2. LowerSemicontinuous objective: the constant-bottom EReal-valued function is globally lower semicontinuous on ℝ.
3. IsCompact feasible: {0} is compact in the ordinary real topology.
4. (feasible ∩ effectiveDomain objective).Nonempty: there exists x:ℝ with x∈{0} and objective(x)<top.
5. objective(0)=bottom.
6. NOT SourceProper objective. Using the supplied definition, this is ¬((∀ x:ℝ, objective(x)≠bottom) ∧ ∃ x:ℝ, ∃ r:ℝ, objective(x)=(r:EReal)).

The six conjuncts are right-associated in the Lean statement. The first existential is scoped only over conjunct 1; it does not bind a variable used by later conjuncts. Lower semicontinuity, compactness, and domain nonemptiness are assertions of this closed example, not external assumptions supplied to the theorem.

## Meaning, consequences, and edge cases

The minimum is attained at 0, the only feasible point. Its value is negative infinity, not a finite embedded real. The domain-intersection witness is also 0: bottom<top suffices, and there is no requirement here for a finite-valued witness. No toReal conversion, real arithmetic, or finite-minimum assertion occurs.

The theorem explicitly asserts failure of properness. For this particular constant-bottom definition, both components required by SourceProper fail: the function is bottom at every real point, and it has no finite real-valued point. The negation in the header is syntactically a negation of the whole conjunction; the stronger observation that each component fails follows from the supplied definition of objective.

IsMinOn alone does not assert membership. Indeed, for this constant function its comparison predicate holds for any real p, even p outside the singleton. The explicit membership in conjunct 1 restricts the existential witness to 0. Consequently the feasible minimizer is unique as a consequence of the singleton definition, but no ExistsUnique proposition is part of the stated conclusion.

The feasible set is nonempty and cannot vary; the theorem does not quantify over arbitrary compact sets or functions. The example exhibits attainment under its asserted compactness, lower semicontinuity, and non-top-domain-intersection facts despite improperness and a bottom minimum. It does not assert any general existence theorem, finite minimum, properness, optimization algorithm, quantitative estimate, or provider invocation.

## Ambiguities and limits

No enclosing namespace is supplied, so only the short theorem name is identifiable. The supplied semantic definitions determine the interpretation; their implementation bodies were not inspected. There is no material ambiguity in conjunction order or quantifier scope. Header text cannot establish how the attainment conjunct is proved or whether a particular provider theorem was used.
