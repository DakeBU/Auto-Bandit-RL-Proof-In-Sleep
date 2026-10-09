# Two let-bound extended-real canary reconstructions

Actor /root/osd_blind; requested GPT-6 Astra / medium. Runtime model and effort are not independently attested. This automated decoder has reused related staged history; no fresh source-naive, absolutely blind, human or externally independent status is claimed. Only the current neutral file was read. These are proposed complete Test types, not supplied Test proofs or compiler evidence. No source fidelity or acceptance is assessed.

## Context and scope

Each theorem defines its own V,f,ψ by local lets whose scope is the entire ensuing conjunction. They are fixed definitions, not universally quantified choices or new library definitions. All spaces here are the real line. Denote the real-to-EReal embedding by ι and put F(z)=(f z).toReal.

Proper(f) means no value is bottom anywhere and at least one ambient point has a finite real value. It permits top. The supplied support predicate is
\[
\partial f(z)=\{g\in\mathbb R:\ \forall y\in\mathbb R,\
f(z)+\iota(g(y-z))\le f(y)\}.
\]
The ambient comparison y is not restricted to V. The statement “for every z∈V, the support set is nonempty” has quantifier order ∀z∈V ∃g ∀y∈R; g may depend on z.

Divergence uses its ordered second argument as base:
\[
D_\psi(a,b)=\psi(a)-\psi(b)-(\operatorname{fderiv}\psi(b))(a-b).
\]
The total derivative convention defaults to zero without differentiability. The generators here are explicit polynomials. No proof of their derivative formulas or of the target assertions is supplied. IsMinOn A V p means ∀z∈V, A(p)≤A(z); it does not supply p∈V, although the concrete point 0 belongs to both displayed intervals. EReal.toReal sends both infinities to zero; finite values retain their real value.

## 1. restricted_absolute_nonquadratic

The exact local definitions are
\[
V=[-1,1],\qquad
f(z)=
\begin{cases}\iota(|z|)&z\in[-1,1],\\+\infty&z\notin[-1,1],\end{cases}
\qquad
\psi(z)=z^4/4+z^2/2.
\]
Thus F(z)=|z| on V and F(z)=0 outside V. There is no bottom value in the definition. Independently counting the top-level conjuncts after the lets gives twelve:

1. f is proper.
2. At every z∈V, f has a global ambient supporting vector.
3. f(2)=+∞.
4. F is convex on V.
5. F is not convex on the whole real line.
6. ψ is strictly convex on the whole real line.
7. Zero minimizes the actual EReal objective f(z)+ι(Dψ(z,1/2)) over V.
8. The real absolute-value function is not ambient differentiable at zero.
9. Dψ(1/2,0)=9/64.
10. Dψ(0,1/2)=11/64.
11. Every feasible u satisfies −|u|≤Dψ(u,1/2)−Dψ(u,0)−Dψ(0,1/2).
12. The separate real numerical inequality −1/2≤−5/16 holds.

In compact LaTeX, with these exact local definitions:
\[
\begin{aligned}
&\operatorname{Proper}(f)\\
&\land[\forall z\in V,\ \partial f(z)\ne\varnothing]\\
&\land f(2)=+\infty\\
&\land\operatorname{ConvexOn}_{\mathbb R}(V,F)\\
&\land\neg\operatorname{ConvexOn}_{\mathbb R}(\mathbb R,F)\\
&\land\operatorname{StrictConvexOn}_{\mathbb R}(\mathbb R,\psi)\\
&\land\operatorname{IsMinOn}(z\mapsto f(z)+\iota(D_\psi(z,\tfrac12)),V,0)\\
&\land\neg\operatorname{DifferentiableAt}_{\mathbb R}(|\cdot|,0)\\
&\land D_\psi(\tfrac12,0)=\tfrac9{64}\\
&\land D_\psi(0,\tfrac12)=\tfrac{11}{64}\\
&\land[\forall u\in V,\ -|u|\le
D_\psi(u,\tfrac12)-D_\psi(u,0)-D_\psi(0,\tfrac12)]\\
&\land(-\tfrac12\le-\tfrac5{16}).
\end{aligned}
\]

1. **Objects:** Fixed scalar V,f,ψ from the lets, F the total real conversion, global subdifferentials, center x=1/2, minimizer p=0 and feasible comparators.
2. **Quantifiers/order:** The lets precede and scope all twelve conjuncts. The support clause has ∀z∈V ∃g ∀ambient y. The comparator clause has ∀u∈V. Other universal quantifiers occur internally in properness, convexity and IsMinOn; there is no outer universal parameter or existentially selected minimizer.
3. **Assumptions/regularity:** There are no premises. Properness, support existence, convexity, strict convexity, minimization and nonsmoothness are asserted parts of the proposed conclusion. The nonsmoothness concerns abs, not the polynomial ψ and not a real derivative of the EReal-valued f.
4. **Conclusion and minimum scope:** All twelve properties are retained. In clause 7 the inequality is in EReal:
\[
\forall z\in V,\quad f(0)+\iota(D_\psi(0,\tfrac12))
\le f(z)+\iota(D_\psi(z,\tfrac12)).
\]
This is not silently replaced by an all-ambient or finite-part minimum. Clause 11 retains two subtracted residuals and the fixed comparator difference −|u|.
5. **Constants/boundaries:** Endpoints −1,1 are included; 2 is outside and really has top value. Both 0 and 1/2 are feasible. Divergence coefficient in the objective is 1, with no extra half factor. The values 9/64 and 11/64 concern opposite argument orders and exhibit asymmetry. u=0 gives zero-versus-zero; u=1/2 corresponds to clause 12's nonzero numerical comparison. Strictness applies to ψ's convexity, not to the non-strict comparator inequality.
6. **Information/extended-real distinction:** Deterministic static objects. Ambient support comparisons include outside y with f(y)=top; finite-part conversion instead makes those outside values zero. Accordingly convexity of F is asserted only on V and explicitly denied globally. Properness does not mean f finite everywhere.
7. **Excluded scope/proof boundary:** No general statement for arbitrary restrictions, no global convexity of F, no symmetry of D, no uniqueness or algorithmic minimizer production, and no Test-body dependency on any public helper are certified. IsMinOn does not manufacture membership. The type itself proves none of the twelve assertions.

## 2. restricted_linear_outside_center

The separate exact local definitions are
\[
V=[0,1],\qquad
f(z)=
\begin{cases}\iota(z)&z\in[0,1],\\+\infty&z\notin[0,1],\end{cases}
\qquad
\psi(z)=z^2/2.
\]
Thus F(z)=z on V and zero outside V. Independently counting the top-level conjuncts gives eleven:

1. f is proper.
2. Every z∈V has a global ambient supporting vector for f.
3. f(−1)=+∞.
4. −1 does not belong to V.
5. F is convex on V.
6. F is not convex on the whole real line.
7. ψ is globally strictly convex.
8. Zero minimizes f(z)+ι(Dψ(z,−1)) over V.
9. Dψ(0,−1)=1/2.
10. Every feasible u satisfies −u≤Dψ(u,−1)−Dψ(u,0)−Dψ(0,−1).
11. The separate numerical inequality −1/2≤1/2 holds.

With precisely these local definitions:
\[
\begin{aligned}
&\operatorname{Proper}(f)\\
&\land[\forall z\in V,\ \partial f(z)\ne\varnothing]\\
&\land f(-1)=+\infty\\
&\land(-1\notin V)\\
&\land\operatorname{ConvexOn}_{\mathbb R}(V,F)\\
&\land\neg\operatorname{ConvexOn}_{\mathbb R}(\mathbb R,F)\\
&\land\operatorname{StrictConvexOn}_{\mathbb R}(\mathbb R,\psi)\\
&\land\operatorname{IsMinOn}(z\mapsto f(z)+\iota(D_\psi(z,-1)),V,0)\\
&\land D_\psi(0,-1)=\tfrac12\\
&\land[\forall u\in V,\ -u\le
D_\psi(u,-1)-D_\psi(u,0)-D_\psi(0,-1)]\\
&\land(-\tfrac12\le\tfrac12).
\end{aligned}
\]

1. **Objects:** New fixed let-bound V,f,ψ, distinct from the first theorem's objects; finite part F; outside center x=−1; boundary minimizer p=0; feasible real comparators u.
2. **Quantifiers/order:** Three lets scope all eleven conjuncts. Supporting vectors are allowed to vary with each feasible z but must support at every ambient y. The comparator binder scopes only clause 10; no universal center or time parameter is supplied.
3. **Assumptions/regularity:** No external premises. All properness, supports, convexities, nonmembership and minimum assertions are proposed conclusions. This theorem has no abs function and no nondifferentiability clause; its feasible loss is linear.
4. **Conclusion and minimum scope:** The EReal minimum assertion means
\[
\forall z\in[0,1],\quad
f(0)+\iota(D_\psi(0,-1))\le f(z)+\iota(D_\psi(z,-1)).
\]
The center's infinite f-value does not enter the regularizer, which uses ψ at the center. Clause 10 has loss difference F(0)−F(u)=−u and exactly the displayed ordered residuals.
5. **Constants/boundaries:** p=0 is an included endpoint; −1 is outside and has top value. All of [0,1], including 1, is feasible. The objective coefficient on D is 1; ψ carries its own factor 1/2. u=0 yields equality; u=1/2 corresponds to the separate nonzero numerical clause. The single explicit divergence value is 1/2; no reversed-divergence value or asymmetry claim appears in this second type.
6. **Information/extended-real distinction:** Deterministic constrained minimization with outside center. SourceProper excludes bottom globally but permits top outside. F converts the outside top values to zero, explaining why “convex on V” must not be promoted to global finite-part convexity. Global support and feasible-only convexity have different scopes.
7. **Excluded scope/proof boundary:** Does not require initial center in V, does not provide an iteration, and does not assert an unconstrained minimum or uniqueness. IsMinOn does not itself include p membership. No abs/nonsmooth claim, arbitrary-domain theorem, actual public-helper dependence, production proof or source acceptance is established.

## Completeness

The full let scopes and all twelve/eleven conjuncts are reconstructed independently, with seven semantic slots for each theorem. No unresolved semantic/type-context question was identified from the supplied context. Source, Test bodies, production code, contracts and compilation were not consulted. The input and output hashes are recorded in the separate receipt; the report does not certify theorem truth or any acceptance stage.
