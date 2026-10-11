# Independent neutral declaration decode

Actor: /root/adaptive_decoder. Requested GPT-6 Astra / medium; runtime not attested. Prior related source exposure exists: this is an independent restricted-input declaration decode, not a fresh source-blind review. Only the two neutral files and frozen public header were read for semantic review; filenames were enumerated. No candidate BODY, design, producer proposal, source expectations, compiler, or proof-term audit was read/run.

## Frozen public theorem: seven slots

1. Objects/types: an arbitrary real normed vector space E (NormedAddCommGroup and NormedSpace ℝ), an extended-real function f, a set V, and real modulus λ. No finite-dimensional, completeness, inner-product, closedness or differentiability requirement appears.
2. Quantifiers: universally parameterized f,V,λ,p,q and all hypotheses. The strong-convexity premise quantifies every x,y in V and every real a with 0<a<1.
3. Domain premises: SourceProper f; V convex; V ⊆ effectiveDomain f; λ≥0. SourceProper and effectiveDomain are imported opaque definitions in these permitted excerpts, so their complete expansions are not independently verified here.
4. Curvature premise: f(a x+(1−a)y) ≤ a f(x)+(1−a) f(y)−(λ/2)a(1−a)‖x−y‖², with coefficients/penalty cast to EReal. This is the supplied strong-convexity condition, not the desired minimum-growth conclusion as an assumption.
5. Minimizer/comparator premises: p∈V and IsMinOn f V p; q∈V. The chosen minimizer is supplied; there is no existence or uniqueness conclusion. In the usual IsMinOn meaning, f(p)≤f(v) for all v∈V.
6. Conclusion/constants: (f p).toReal+(λ/2)‖q−p‖²≤(f q).toReal. The exact factor is λ/2 and displacement is q−p; λ=0 is admitted.
7. Causality/boundary: static geometric statement with no time index, trajectory, selector, algorithm, probability, terminal convention or regret. EReal-to-real conversion is explicitly part of the conclusion; safe conversion relies on the imported proper/domain conditions, whose definitions are not shown here.

## square_two_exact_growth: seven slots

1. Objects: E=ℝ; squareLoss(x) is the EReal coercion of the real square x².
2. Quantifiers: theorem has no explicit hypotheses or arguments. Its first and second conjuncts each quantify independently every q∈ℝ.
3. Hypotheses: no implication antecedent can make the assertion vacuous; all values are finite by the explicit definition.
4. First conclusion: for every q, squareLoss(0).toReal+(2/2)‖q−0‖²≤squareLoss(q).toReal; conventionally this is q²≤q².
5. Second conclusion: the same expression equals squareLoss(q).toReal for every q. It records exact saturation of the coefficient λ=2 at p=0, rather than only one selected comparator.
6. Third conclusion: the closed proposition (9:ℝ)≤9. This is tautological; the header does not connect it syntactically to q=3 or to a theorem application. It adds no further constraint on the core.
7. Core-semantic reach: the first conjunct has the shape of the core specialized to f=squareLoss, V=univ, λ=2, p=0, arbitrary q. V and proof obligations are not present in this canary header, so this is a proposed matching instantiation, not verified consumption. The equality constrains the example’s numerical normalization, but neither conjunct forces the implementation to use the core. Direct consumer linkage requires a subsequent BODY/VALUE review. No temporal or algorithmic claim occurs.

## interval_zero_extended_domain: seven slots

1. Objects: intervalLoss is imported extendedIndicator applied to [0,1]⊂ℝ; its complete definition is not expanded in the neutral context.
2. Quantifiers: a closed theorem with no arguments or hypotheses. Four conjuncts must all hold.
3. First conclusion: intervalLoss(0).toReal+(0/2)‖1−0‖²≤intervalLoss(1).toReal. Under the conventional zero-inside/top-outside indicator definition this is 0≤0, testing the admitted λ=0 boundary at distinct points p=0 and q=1.
4. Second conclusion: intervalLoss(2)=⊤, explicitly requiring an extended-real value outside the intended feasible interval.
5. Third conclusion: effectiveDomain(intervalLoss)=[0,1] exactly; this asserts both inclusions, not just feasibility of 0 and 1.
6. Fourth conclusion: IsMinOn intervalLoss [0,1] 0, asserting the chosen point minimizes over the whole interval. IsMinOn itself should not be mistaken for a separately displayed membership premise, although 0∈[0,1] is true. No uniqueness is asserted.
7. Core-semantic reach: the first conjunct matches λ=0, V=[0,1], p=0, q=1 once all core premises are constructed. Other conjuncts constrain the actual extended-domain example and prevent replacing it by a globally finite zero function. They do not establish all SourceProper/strong-convexity premises or force core consumption in the signature. No conclusion evaluates toReal at the exterior point 2; thus the displayed inequality does not exploit totalized conversion of ⊤. Again direct core reuse must be checked later.

## Findings and bounded verdict

Both public statements are non-vacuous concrete examples; the universal square equality and exact interval domain/top/minimum conjuncts are meaningful. The standalone 9≤9 conjunct is redundant and has no additional semantic force. No extra assumption or axiom declaration appears in the allowed neutral text. This does not certify absence of axioms in imports or future proofs: that requires the actual dependency/axiom audit. Definitions of SourceProper, effectiveDomain, and extendedIndicator are imported but omitted, so their full semantics remain a context dependency, not independently inspected evidence.

Verdict: reconstructed with explicit limitations; no contradiction or empty-antecedent defect found. This decode does not authorize compilation, accept source fidelity, verify direct consumers, or accept any BODY/package. Later review must verify that each first conjunct actually consumes stronglyConvex_minimum_growth with lawful properness/domain/curvature/minimum premises, rather than an unused call or an independently proved bound.
