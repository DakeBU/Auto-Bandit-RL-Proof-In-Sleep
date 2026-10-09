# Three proximal comparison canary types: neutral reconstruction

Actor /root/osd_blind; requested GPT-6 Astra / medium. Runtime model and effort are not independently attested. This reused automated decoder has prior staged history, including the earlier neutral helper header. It is not a fresh source-naive, absolutely blind, human, or externally independent actor. Only the current canary input was newly read; the earlier neutral header supplies allowed contextual meaning. No source, review verdict, or production proof body was consulted in this decode.

These are proposed theorem types, not supplied proofs. IsMinOn F V p means that F(p)≤F(z) for every z∈V; it does not itself assert p∈V. In these concrete instances membership is mathematically fixed by the displayed points and sets, but it is not a separate conjunct and must not be attributed to the definition of IsMinOn. The contextual helper requires membership explicitly when applied. A matching numerical conclusion or import does not establish proof-term dependence on that helper; an eventual body/dependency inspection would be required.

## 1. nonsmooth_shifted_quadratic

The sum of absolute value and the shifted quadratic is minimized at zero over the entire real line. Absolute value is not differentiable at zero. Every real comparator u satisfies −|u|≤−u/2, and the separate numerical inequality −1/4≤−1/8 holds.

\[
\begin{aligned}
&\operatorname{IsMinOn}_{\mathbb R}
\left(z\mapsto |z|+\frac{(z-\frac12)^2}{2},\,0\right)\\
&\quad{}\land \neg\operatorname{DifferentiableAt}_{\mathbb R}(|\cdot|,0)\\
&\quad{}\land [\forall u\in\mathbb R,\ -|u|\le -u/2]
\land (-1/4\le-1/8).
\end{aligned}
\]
The first conjunct expands to
\[
\forall z\in\mathbb R,\quad
|0|+\frac{(0-\frac12)^2}{2}
\le |z|+\frac{(z-\frac12)^2}{2}.
\]

1. **Objects:** Scalar domain R, point p=0, f(z)=|z|, h(z)=(z−1/2)²/2 and their sum, plus real comparators u.
2. **Quantifiers/order:** Four closed conjuncts, with the third universally quantified over u. The first has the universal comparison internal to IsMinOn. No assumed minimizer premise is provided: its minimization is itself asserted.
3. **Assumptions/regularity:** No external hypotheses. The nondifferentiability assertion concerns f=abs at p, not h. No derivative or convexity premise is explicitly included in this canary.
4. **Conclusion:** Global minimization of f+h at 0, failure of differentiability of abs there, the all-real comparison inequality, and a separate numerical inequality.
5. **Constants/boundaries:** Shift 1/2 and quadratic denominator 2; numeric denominators 4 and 8 are nonzero reals. u=0 gives equality in the universal comparison. The numeric comparison corresponds to u=1/4, but the type writes it as its own conjunct, not a proof of instantiation.
6. **Information/helper interpretation:** Deterministic. In the allowed helper notation, f(p)−f(u)=−|u| and the derivative of the displayed h at p would act as v↦−v/2. This explains the intended expression correspondence without claiming the header proves the derivative or uses the helper.
7. **Excluded claims/proof boundary:** IsMinOn is not a membership producer, although 0∈univ. This is not a claim that f is differentiable, nor a general theorem for all shifts. The numerical clause does not certify dependence on the imported helper; no body or source verdict is supplied.

## 2. boundary_linear_regularizer

The function z↦z+(−z/2) is minimized at zero on the closed interval [0,1]. Every feasible comparator u in that interval satisfies −u≤−u/2. The same point is not a minimizer of that same function over the whole real line.

\[
\operatorname{IsMinOn}_{[0,1]}(z\mapsto z-z/2,0)
\ \land\
[\forall u\in[0,1],\ -u\le-u/2]
\ \land\
\neg\operatorname{IsMinOn}_{\mathbb R}(z\mapsto z-z/2,0).
\]
Equivalently, the minimization and its negation compare the value zero at p=0 with z/2 on their respective domains:
\[
[\forall z\in[0,1],\ 0\le z/2]\ \land\
[\forall u\in[0,1],\ -u\le-u/2]\ \land\
\neg[\forall z\in\mathbb R,\ 0\le z/2].
\]

1. **Objects:** f(z)=z, h(z)=−z/2, point p=0, constrained domain [0,1], and a separate whole-line minimization test for the identical sum.
2. **Quantifiers/order:** Three conjuncts. The middle universally quantifies u then its interval membership; the last negates the entire whole-line IsMinOn predicate.
3. **Assumptions/regularity:** No external premises. The comparator membership is local to the middle clause, not a condition that modifies the final whole-line test. No convexity or differentiability property is separately asserted.
4. **Conclusion:** Constrained minimization and all-feasible comparison, together with failure of unconstrained minimization at the same point.
5. **Constants/boundaries:** p=0 is the left endpoint and is included in [0,1]. u=0 gives equality; u=1 gives the nonzero inequality −1≤−1/2. The header contains no separate numerical inequality conjunct in this case. Denominator 2 is fixed.
6. **Information/helper interpretation:** Deterministic constraint-sensitive statement. The helper correspondence uses f(p)−f(u)=−u and the linear derivative v↦−v/2. The domain is not required to provide an interior neighborhood around p; the constrained minimum does not assert an ambient stationary point.
7. **Excluded claims/proof boundary:** IsMinOn alone does not supply 0∈[0,1], although the concrete membership holds. Negating the whole-line minimum at 0 does not negate the interval minimum. No proof of either, no uniqueness assertion, and no actual helper-dependency evidence is supplied.

## 3. nonconvex_regularizer

The function z↦z²+(−z²/2+z) is minimized at −1 over all reals. Its second component h(z)=−z²/2+z is not convex on the whole real line. Every real u satisfies 1−u²≤2(u+1), and the separate numeric inequality 1≤2 holds.

Crucially, the input expression −z ^ 2 parses as the negative of the square, −(z²), not as (−z)². Thus h(z)=−(z²)/2+z and f(z)+h(z)=z²/2+z.

\[
\begin{aligned}
&\operatorname{IsMinOn}_{\mathbb R}
\left(z\mapsto z^2+\left(-\frac{z^2}{2}+z\right),-1\right)\\
&\quad{}\land\neg\operatorname{ConvexOn}_{\mathbb R}
\left(\mathbb R,z\mapsto-\frac{z^2}{2}+z\right)\\
&\quad{}\land[\forall u\in\mathbb R,\ 1-u^2\le2(u+1)]
\land(1\le2).
\end{aligned}
\]
The first conjunct means
\[
\forall z\in\mathbb R,\quad
(-1)^2+\left(-\frac{(-1)^2}{2}-1\right)
\le z^2+\left(-\frac{z^2}{2}+z\right).
\]

1. **Objects:** Scalar functions f(z)=z² and h(z)=−z²/2+z, their sum, point p=−1, domain R, and real comparators u.
2. **Quantifiers/order:** Four conjuncts: minimum of the sum, nonconvexity of h, all-real comparator inequality, and independent numeric inequality. The all-u binder scopes the third conjunct only.
3. **Assumptions/regularity:** No supplied hypotheses. The type asserts nonconvexity of h; it does not assume it or assert nonconvexity of f+h. No derivative premise is present in this canary header.
4. **Conclusion:** Global minimum at −1 for the sum, failure of global convexity for h alone, the universal comparison, and 1≤2.
5. **Constants/boundaries:** The negative quadratic coefficient is −1/2, not +1/2. At u=p=−1 the comparison reads 0≤0. The nonzero numeric clause corresponds to u=0, giving 1≤2. No restricted comparator domain or empty-domain case occurs.
6. **Information/helper interpretation:** Deterministic. For the permitted helper correspondence, f(p)−f(u)=1−u², displacement is u−p=u+1, and the derivative of h at p would act as v↦2v. This interpretation explains the sign and factor without establishing an application proof.
7. **Excluded claims/proof boundary:** Nonconvexity is about h on univ, not the total objective. IsMinOn does not assert membership by itself; −1∈univ is separate mathematical context. No claim of uniqueness, actual derivative proof, source correspondence, or dependency of the numerical value on the public helper is made.

## Completeness and status

All three proposed types have complete natural-language, LaTeX, and seven-slot reconstructions. No unresolved semantic/type-context ambiguity was identified. The earlier neutral helper is used only as permitted contextual background, not as accepted proof or a newly inspected artifact. The current sole input's raw hash is checked before and after. Source, proof, compilation, and theorem-body dependency acceptance are not assessed.

