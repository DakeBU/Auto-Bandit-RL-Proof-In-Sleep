# Five cumulative Option-run statements: neutral reconstruction

Actor /root/osd_blind; requested GPT-6 Astra / medium. Runtime model and effort are not independently attested. This is a reused automated actor with related staged mathematical history, not absolutely blind, human, externally independent or fresh source-naive. Only neutral-statement-packet-v2.json was read; no earlier packet or verdict was inherited as evidence. These proposed headers are reconstructed without proof, compilation or source acceptance.

## Exact objects, definitions and common assumptions

Every theorem is universally quantified over E:Type with NormedAddCommGroup E, InnerProductSpace R E and CompleteSpace E. No finite dimension is assumed. V and X are sets in E; V is convex in every theorem. Write ℓ_t:E→EReal for loss t, and ι for the real embedding.

The packet's divergence is
\[
D(a,b)=\psi(a)-\psi(b)-(\operatorname{fderiv}_{\mathbb R}\psi(b))(a-b).
\]
The second point is the derivative base. The total derivative uses the zero default if not differentiable. Here the relevant state bases are constrained to interior X with DifferentiableOn ψ (interior X); since this set is open, these conditions express actual ambient differentiability there. ψ has no convexity assumption in the first three statements. Differentiability at the comparator u is never required.

The canonical advance tests whether there exists p∈V minimizing
\[
z\mapsto\ell_t(z)+\iota(\eta_t^{-1}D(z,a))
\]
over V, returning some of a Classical.choose witness if one exists, otherwise none. IsMinOn means comparison with every feasible z and does not itself supply membership; the branch separately requires p∈V. This is a noncomputable selection, not an implemented numerical optimizer.

The canonical iterate is I0=some x0 and I_(t+1)=I_t.bind(advance with η_t and ℓ_t). Hence no recovery from none occurs in the definition. Each statement assumes a supplied trajectory x:N→E agrees with the actual successful recursion:
\[
S_T:\quad \forall t\le T,\ I_t=\mathrm{some}(x_t).
\]
This includes x_0=x0 and feasibility of updated x_t for 1≤t≤T; it does not separately require the initial x0∈V. States x_t past T are unrestricted. It is not an arbitrary trace satisfying only membership.

All five statements also assume
\[
H_T:\quad\forall t\le T,\ x_t\in\operatorname{int}X,\qquad
\operatorname{DifferentiableOn}_{\mathbb R}(\psi,\operatorname{int}X).
\]
For each t<T they require proper loss and nonempty globally supporting sets:
\[
P_T:\quad
\forall t<T,\quad
[(\forall y\in E,\ \ell_t(y)\ne-\infty)
\land(\exists a\in E,\exists r\in\mathbb R,\ell_t(a)=\iota(r))],
\]
\[
G_T:\quad
\forall t<T,\ \forall z\in V,\ \exists g\in E,\ \forall y\in E,\quad
\ell_t(z)+\iota(\langle g,y-z\rangle)\le\ell_t(y).
\]
The support comparison is over all ambient y, not just V. Supports may vary with t,z. The properness witness need not be feasible. These hypotheses exclude bottom everywhere and supply finite feasible-loss semantics through global support; top outside V is allowed. The bare total toReal map sends infinities to zero, so replacing extended losses by real values without these conditions would change the interpretation.

For all statements u is an arbitrary fixed comparator in V, chosen after the run/horizon assumptions. Define
\[
L_T(u)=\sum_{t=0}^{T-1}[(\ell_t(x_{t+1})).\mathrm{toReal}-(\ell_t(u)).\mathrm{toReal}],
\quad A_t=D(u,x_t),\quad B_t=D(x_{t+1},x_t).
\]
This is a signed, unnormalized, same-path finite cumulative loss difference. Each scored x_(t+1) has already consumed the current loss ℓ_t; I_t uses strict-past losses and steps. There is no pre-current-loss action, probability, expectation, minimization over u, or convergence claim. Steps, losses and initialization are supplied parameters; their external choice is not constrained by a data-generation protocol.

## 1. iterate_divergence_sum

For any step stream positive at all played indices, any horizon T (including zero), and the actual successful interior trajectory with proper globally supported losses, the cumulative difference is bounded by the sum of weighted comparator-divergence differences minus the weighted movement divergences.
\[
L_T(u)\le
\sum_{t<T}\frac{A_t-A_{t+1}}{\eta_t}
-\sum_{t<T}\frac{B_t}{\eta_t}.
\]

1. **Objects:** Complete real inner-product E; V,X,ψ,η:N→R,ℓ,x0,x:N→E,T and feasible u, with A,B,L as defined.
2. **Quantifiers/order:** V,X,hV,ψ,hd,η,loss,x0,x,T; then S_T,H_T, positivity, P_T,G_T; finally u,hu. All are universal and there is no existence output.
3. **Assumptions:** Common conditions above and ∀t<T,η_t>0. No monotonicity, ψ convexity, V⊆X or initial feasibility is stipulated.
4. **Conclusion:** Exactly the weighted finite-sum inequality displayed; the first numerator is a difference, and the entire movement sum is subtracted.
5. **Constants/boundaries:** Divisor η_t, not 2η_t; index range 0,…,T−1 and final state x_T. T=0 gives empty sums and 0≤0; S_0 and H_0 still require x_0=x0 and x0∈interior X. Positivity/properness/support assumptions are then vacuous.
6. **Information:** Same actual successful recursion for the supplied η stream. Only played steps need positivity. No conditions on future losses or η_T.
7. **Excluded scope:** Neither A nor B is asserted nonnegative here. No unweighted telescoping identity for variable η is stated, and no success/existence theorem is produced.

## 2. iterate_fixed_sharp

With one fixed positive real η used in the entire recursion, retain the terminal comparator divergence and total movement subtraction:
\[
L_T(u)\le\frac{D(u,x0)}{\eta}
-\frac{A_T}{\eta}
-\frac{\sum_{t<T}B_t}{\eta}.
\]

1. **Objects:** Same complete-space/domain/function context, now η:R constant and I defined with the constant step stream.
2. **Quantifiers/order:** V,X,hV,ψ,hd,η,hη,loss,x0,x,T,S_T,H_T,P_T,G_T,u,hu.
3. **Assumptions:** η>0 even at T=0; common trajectory, interior, properness and support conditions. No ψ convexity or V⊆X.
4. **Conclusion:** Initial D(u,x0) minus terminal D(u,x_T) minus the sum of D(x_(t+1),x_t), all with the same η denominator.
5. **Constants/boundaries:** T may be zero. S_0 identifies x_0 with x0, so RHS is zero then. Terminal x_T is the last scored point for positive T, not x_(T+1). No factor 1/2.
6. **Information:** Fixed η is used in both actual run and bound; the initial center is not silently replaced by a projected initial point.
7. **Excluded scope:** No nonnegativity assumption permits discarding terminal/movement terms from this header alone. No produced run or arbitrary-trace bound.

## 3. iterate_variable_sharp

For positive T and played positive nonincreasing steps, suppose a supplied real M bounds A_t for every pre-update state index t<T. Then
\[
L_T(u)\le
\frac{M}{\eta_{T-1}}
-\frac{A_T}{\eta_{T-1}}
-\sum_{t<T}\frac{B_t}{\eta_t}.
\]

1. **Objects:** Step stream and comparator-dependent finite bound M:R, in addition to V,X,ψ,loss,x0,x,T,u.
2. **Quantifiers/order:** V,X,hV,ψ,hd,η,loss,x0,x,T,hT,S_T,H_T,hη,hmono,P_T,G_T,u,hu,M,hbound. M is supplied after the comparator and can depend on that comparator/run/horizon.
3. **Assumptions:** T>0; η_t>0 for t<T; ∀t, t+1<T→η_(t+1)≤η_t; common conditions; and ∀t<T,A_t≤M. No assumption M≥0, no ψ convexity and no V⊆X.
4. **Conclusion:** Bound with both initial-bound and terminal terms divided by the last played step η_(T−1), while movement terms use their own η_t.
5. **Constants/boundaries:** The bound on A excludes terminal index T and includes initial index 0. T−1 is natural subtraction, safe as a last played index because T>0. T=1 makes monotonicity vacuous; requires only A0≤M and η0>0. η_T is neither used nor constrained.
6. **Information:** Same η-dependent successful run; M is a bound on its own trajectory rather than a separate run. No tuning or horizon-independent bound is asserted.
7. **Excluded scope:** Not a zero-horizon theorem and not a maximum over indices through T. Signed divergences and M remain allowed; residuals are retained.

## 4. iterate_fixed_regret

Add V⊆X and strict convexity of ψ on X to the fixed-step hypotheses. The stated bound removes the terminal comparator-divergence term but retains the full movement subtraction:
\[
L_T(u)\le\frac{D(u,x0)}{\eta}
-\frac{\sum_{t<T}B_t}{\eta}.
\]

1. **Objects:** Fixed positive η, V⊆X, strictly convex generator on X, successful interior trajectory and feasible comparator.
2. **Quantifiers/order:** V,X,hV,hVX,ψ,hc,hd,η,hη,loss,x0,x,T,S_T,H_T,P_T,G_T,u,hu.
3. **Assumptions:** Every fixed-sharp condition, plus inclusion V⊆X and StrictConvexOn R X ψ. These latter premises are explicit, not silently inserted into the first three theorems. No closedness or finite dimension.
4. **Conclusion:** Initial divergence/η minus movement sum/η. No terminal subtraction in this exact type.
5. **Constants/boundaries:** T=0 is included: L0=0 and the bound is 0≤D(u,x0)/η, not the zero RHS of fixed_sharp. hu,hVX put u in X; H_0 puts x0 in interior X. No positivity of T.
6. **Information:** Same constant-step actual run. Convexity is on X, with states inside interior X and comparator in V⊆X; it need not be global on E.
7. **Excluded scope:** Strict convexity does not make the final inequality strict. No assertion of uniqueness, attainment, rates, asymptotic no-regret or a new iterate implementation.

## 5. iterate_variable_regret

With positive T, positive played nonincreasing steps, V⊆X and strict convexity of ψ on X, replace M by the actual finite maximum of the comparator divergences at indices 0 through T−1:
\[
L_T(u)\le
\frac{\max_{0\le t<T}D(u,x_t)}{\eta_{T-1}}
-\sum_{t<T}\frac{D(x_{t+1},x_t)}{\eta_t}.
\]

1. **Objects:** Same complete real inner-product setting, variable-step actual run and fixed feasible u; a finite maximum defined by Finset.sup' of range T.
2. **Quantifiers/order:** V,X,hV,hVX,ψ,hc,hd,η,loss,x0,x,T,hT,S_T,H_T,hη,hmono,P_T,G_T,u,hu. No separate M or hbound input.
3. **Assumptions:** T>0, common successful/interior and loss assumptions, positivity before T, monotonicity only when t+1<T, V⊆X and strict convexity on X.
4. **Conclusion:** The finite nonempty supremum/maximum over A0,…,A_(T−1) divided by the last played η_(T−1), minus weighted movement sum. The terminal comparator term is absent.
5. **Constants/boundaries:** sup' uses an explicit nonempty-range witness from T>0; it has no arbitrary default for an empty range. It is neither an infinite supremum nor a maximum including x_T. At T=1 the maximum is D(u,x0); η1 is irrelevant.
6. **Information:** The maximum is taken along the very same successful η-dependent trajectory, for this comparator. No future state or alternate choice of η enters it. The result is finite-horizon and unnormalized.
7. **Excluded scope:** No T=0 extension, universal bound independent of comparator/horizon, sum-to-expectation replacement, source interpretation, or proof of the theorem is supplied.

## Completeness and issues

All five precise headers and all five canonical definitions were used. The seven slots for each statement preserve the actual successful Option trajectory, current-loss scoring, global ambient support, finite-part semantics, endpoint signs and played-step indices. No unresolved semantic-context question or internal scope ambiguity was identified in the v2 packet. This is a semantic reconstruction, not a demonstration that the statements have values/proofs or compile.

Per-statement SHA256 values are bound in the receipt exactly as supplied and independently recomputed from the UTF-8 exact_header strings. The immutable packet's raw bytes are checked before and after. File metadata inside the packet was not used as authorization to read any production file.
