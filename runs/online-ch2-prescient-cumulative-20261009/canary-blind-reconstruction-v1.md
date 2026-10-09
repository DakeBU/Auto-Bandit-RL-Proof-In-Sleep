# Two cumulative canary conjunctions: neutral reconstruction

Actor /root/osd_blind; requested GPT-6 Astra / medium, with no independent runtime model/effort attestation. This reused automated actor has related staged history, including a neutral definition of SourceClosed. It is not absolutely blind, fresh source-naive, human or externally independent. Only the current canary packet was read; earlier verdicts, source and proof files were not consulted. All assertions below describe proposed types, not established proofs or minimum-attainment evidence.

## Definitions and common scope

Each target has local lets, fixed for its entire conjunction. Both use
\[
V=[-1,1],\quad \psi(z)=z^4/4+z^2/2,\quad
f_0(z)=\begin{cases}\iota(|z|)&z\in V\\+\infty&z\notin V,\end{cases}
\quad x_t=\begin{cases}0&t=1\\1/2&t\ne1.\end{cases}
\]
The two f1 functions differ and must not be identified. In either target loss0=f0 and loss_t=f1 for all t>0. Here ι embeds R into EReal; finite-part conversion toReal retains finite values and maps infinities to zero. On feasible comparators the displayed f0/f1 values are finite; outside V they are genuinely top, not zero losses.

The packet defines D(a,b)=ψ(a)−ψ(b)−fderiv ψ b(a−b), with b as base. advance selects a feasible global minimizer of loss(z)+ι(η⁻¹D(z,center)) by Classical.choose if one exists; otherwise it is none. Membership is explicit in that existential and not supplied by IsMinOn alone. iterate has I0=some x0 and I_(t+1)=I_t.bind(current advance with η_t,loss_t). Thus matching x_t to the actual run is a substantive assertion, not just a definition of an arbitrary comparison trace. No minimum proof or theorem body is present.

Proper f means no bottom at any ambient point and some finite real witness. Nonempty SourceSubdifferential at z means there exists a real g such that f(z)+ι(g(y−z))≤f(y) for every ambient real y, including outside V. Its quantifier order is ∀z∈V ∃g ∀y∈R, not just supporting comparisons within V.

The packet does not repeat SourceClosed's definition; disclosed retained neutral context supplies its exact meaning: ∀r∈R, the ambient sublevel set {z:F(z)≤ι(r)} is closed. Here it applies to F=ι∘ψ, not to the losses or feasible set. StrictConvexOn and DifferentiableOn both have domain univ in these targets. No external lookup or production-identity verification was performed.

For either target define
\[
L(u)=\sum_{t<2}[(\mathrm{loss}_t(x_{t+1})).\mathrm{toReal}
-(\mathrm{loss}_t(u)).\mathrm{toReal}],\quad
A_t(u)=D(u,x_t),\quad B_t=D(x_{t+1},x_t).
\]
Each scored point is after the current loss has been used. The bound is signed, unnormalized, deterministic, with the same fixed comparator across two rounds. There is no best-comparator infimum or expectation.

## 1. fixed_signed_run

The remaining local definition is
\[
f_1(z)=\begin{cases}\iota(-5z/8)&z\in V\\+\infty&z\notin V.\end{cases}
\]
The actual run uses constant η=1 and starts at 1/2. Independent counting gives sixteen top-level conjuncts:

1. Proper(f0).
2. Proper(f1).
3. Every feasible point has a global support for f0.
4. Every feasible point has a global support for f1.
5. SourceClosed(ι∘ψ).
6. StrictConvexOn R univ ψ.
7. DifferentiableOn R ψ univ.
8. For every t≤2, the actual iterate at t equals some x_t.
9. D(−1/2,x2)=5/8.
10. D(x1,x0)=11/64.
11. D(x2,x1)=9/64.
12. Every feasible comparator satisfies the weighted divergence-difference sum bound with denominators 1.
13. Every feasible comparator satisfies the fixed sharp bound retaining terminal subtraction.
14. Every feasible comparator satisfies the fixed bound omitting terminal subtraction.
15. −9/8≤−5/16.
16. −9/8≤5/16.

The full mathematical conjunction is
\[
\begin{aligned}
&\operatorname{Proper}(f_0)\land\operatorname{Proper}(f_1)
\land[\forall z\in V,\partial f_0(z)\ne\varnothing]
\land[\forall z\in V,\partial f_1(z)\ne\varnothing]\\
&\land\operatorname{SourceClosed}(\iota\circ\psi)
\land\operatorname{StrictConvexOn}(\mathbb R,\psi)
\land\operatorname{DifferentiableOn}(\psi,\mathbb R)\\
&\land[\forall t\le2,\ I_t(V,\psi,(1)_s,\mathrm{loss},1/2)=\mathrm{some}(x_t)]\\
&\land A_2(-1/2)=5/8\land B_0=11/64\land B_1=9/64\\
&\land[\forall u\in V,\ L(u)\le\sum_{t<2}(A_t(u)-A_{t+1}(u))/1-\sum_{t<2}B_t/1]\\
&\land[\forall u\in V,\ L(u)\le D(u,1/2)/1-A_2(u)/1-(\sum_{t<2}B_t)/1]\\
&\land[\forall u\in V,\ L(u)\le D(u,1/2)/1-(\sum_{t<2}B_t)/1]\\
&\land(-9/8\le-5/16)\land(-9/8\le5/16).
\end{aligned}
\]

1. **Objects:** Six fixed lets V,ψ,f0,f1,loss,x; the same actual constant-step Option run; all feasible u. All objects are scalar.
2. **Quantifiers/order:** No external hypotheses. Sixteen asserted conjuncts; supports have nested global comparisons, run agreement quantifies t≤2, and each of the three loss bounds separately quantifies u∈V.
3. **Regularity/minimum assumptions:** Properness, supports, global closed-sublevel/strict-convex/differentiable generator properties and successful trajectory are conclusions. No separate actual minimum proof, existence proof, or noncomputable selection specification proof is supplied by the header.
4. **Conclusion/signs:** All sixteen clauses as listed. Terminal divergence 5/8 is positive but appears with a negative sign in the sharp expression. Movement terms 11/64 and 9/64 are both subtracted; no interchange of their ordered bases.
5. **Constants/indices:** T=2, x0=1/2,x1=0,x2=1/2; denominators are exactly 1. Their movement sum is 20/64=5/16. For u=−1/2, initial and terminal divergences are both 5/8; retaining the negative terminal yields RHS −5/16, dropping it yields +5/16. The literal final clauses are separate numerical inequalities; they correspond to the cumulative loss value −9/8 at that comparator, but no proof of specialization is supplied.
6. **Information/finite boundary:** Round 0 uses abs and outputs 0; round 1 uses −5z/8 and outputs 1/2. Actual equality is asserted only through time 2, although x and loss are defined at all times. No successful future run is asserted. All comparator endpoints of V are included.
7. **Excluded claims:** Neither a nonnegative regret requirement nor equality between loss and energy is claimed. This is not an arbitrary-horizon theorem or proof that the numeric clauses use any public helper. Imported headers describe proposed interfaces, not body evidence.

## 2. decreasing_signed_run

Here f1 is changed, not merely the step schedule:
\[
f_1(z)=\begin{cases}\iota(-5z/4)&z\in V\\+\infty&z\notin V,\end{cases}
\qquad
\eta_t=\begin{cases}1&t=0\\1/2&t>0.\end{cases}
\]
V,ψ,f0,loss and x have the forms stated above, using this new f1. Let
\[
W=\sum_{t<2}\frac{B_t}{\eta_t},\qquad
M(u)=\max_{t\in\{0,1\}}A_t(u).
\]
Finset.sup' on range 2 is this finite nonempty maximum; it is not a supremum including the terminal state index 2.

Independent counting gives twenty-two conjuncts: the same seven proper/support/generator properties as above; η0=1; η1=1/2; positivity for t<2; adjacent monotonicity when t+1<2; actual run equality through t=2; A2(−1/2)=5/8; A1(−1/2)=9/64; W=29/64; M(−1/2)=5/8; M(1/2)=9/64; A0(1/2)=0; an all-feasible sharp maximum bound; an all-feasible terminal-dropped maximum bound; and the two numerical inequalities.

\[
\begin{aligned}
&\operatorname{Proper}(f_0)\land\operatorname{Proper}(f_1)
\land[\forall z\in V,\partial f_0(z)\ne\varnothing]
\land[\forall z\in V,\partial f_1(z)\ne\varnothing]\\
&\land\operatorname{SourceClosed}(\iota\circ\psi)
\land\operatorname{StrictConvexOn}(\mathbb R,\psi)
\land\operatorname{DifferentiableOn}(\psi,\mathbb R)\\
&\land\eta_0=1\land\eta_1=1/2
\land[\forall t<2,\eta_t>0]
\land[\forall t,\ t+1<2\Rightarrow\eta_{t+1}\le\eta_t]\\
&\land[\forall t\le2,\ I_t(V,\psi,\eta,\mathrm{loss},1/2)=\mathrm{some}(x_t)]\\
&\land A_2(-1/2)=5/8\land A_1(-1/2)=9/64
\land W=29/64\\
&\land M(-1/2)=5/8\land M(1/2)=9/64\land A_0(1/2)=0\\
&\land[\forall u\in V,\ L(u)\le M(u)/\eta_1-A_2(u)/\eta_1-W]\\
&\land[\forall u\in V,\ L(u)\le M(u)/\eta_1-W]\\
&\land(-7/4\le-29/64)\land(-1/2\le-11/64).
\end{aligned}
\]

1. **Objects:** Seven local lets including the variable step stream, new linear f1, same displayed states, actual Option run, finite maxima for each comparator and weighted movement W.
2. **Quantifiers/order:** Twenty-two asserted conjuncts with no outer premises. Positivity is all t<2, monotonicity is all t with t+1<2, and actual equality includes t=2. The two final general bounds each independently quantify every u∈V.
3. **Regularity/minimum assumptions:** The seven proper/support/generator properties and successful selected trajectory are conclusions to be proved, not proof evidence. The nonempty-range witness “by decide” only inhabits a finite-set side condition; it is not a proof of a canary or of minimum attainment.
4. **Conclusion/signs:** Retain both maximum bounds, one subtracting terminal A2/η1 and the other not; both subtract W. Distinguish terminal A2(−1/2)=5/8 from middle-state A1(−1/2)=9/64. The same-path maximum is positive at u=1/2 even though its initial A0 is zero.
5. **Constants/indices:** η1 is the last played step 1/2, not η2. The first movement is weighted by 1, the second by 1/(1/2)=2, giving 11/64+18/64=29/64. M uses only x0,x1. For u=−1/2 its value 5/8 equals the terminal 5/8, so the sharp RHS is −29/64 and the corresponding cumulative value is −7/4. For u=1/2, M=9/64 but A0=0; the terminal-dropped RHS is (9/64)/(1/2)−29/64=−11/64, with corresponding cumulative value −1/2. These identify the proposed numbers without supplying minimum or theorem proofs.
6. **Information/finite boundary:** Current second loss is −5z/4, not −5z/8. This change matters for the actual run under the smaller second step. Future coordinates are defined but no actual equality beyond time 2 is asserted. The maximum has two entries, no empty case or default value, and no terminal index entry. Global supporting comparisons include outside top-valued points.
7. **Excluded claims:** Cannot replace the maximum by the initial divergence (the supplied u=1/2 values explicitly separate them), omit the η1 division, or replace weighted movement by the unweighted 5/16 sum. No arbitrary step schedule, empty-horizon extension, all-time success, proof dependency, compilation or source acceptance is asserted.

## Semantic completion and evidence boundary

Both full conjunctions and every local let are reconstructed, with sixteen and twenty-two top-level clauses respectively and seven semantic slots each. No unresolved mathematical-context question was identified using the explicitly disclosed retained SourceClosed meaning; that predicate's definition is not repeated in the current packet.

The five contextual cumulative headers do not prove either canary. Neither numeric inequalities nor listed actual-state equalities supply the missing minimizer/selection proof bodies. No source or production/Test file was opened. The receipt binds the raw packet and independently computed exact-header UTF-8 hashes, and records the limited reconstruction status.
