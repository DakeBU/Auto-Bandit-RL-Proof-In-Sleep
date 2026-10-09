# Seven type-only terminal reconstructions

Actor /root/osd_blind; requested GPT-6 Astra / medium, without independently attested runtime model or reasoning effort. This automated decoder has reused staged history; it is not absolutely blind, human, or externally independent. The present reading uses the two frozen neutral inputs and the necessary Domain/project definitions in the explicitly permitted import. A targeted lookup displayed lines 28–49 of that import; only Domain and project are used here. No source identity, external reference, proof body, or prior verdict was sought.

The input is a text packet containing draft theorem headers, not a compilable Lean file with supplied theorem bodies. The word “theorem” and descriptive declaration names are not proof evidence. This report reconstructs proposed propositions without proving or compiling them.

## Complete shared objects and recursion

E is an arbitrary complete real inner-product space, with NormedAddCommGroup, InnerProductSpace R, and CompleteSpace instances. Finite dimension is not assumed. The imported Domain E bundles a carrier V⊆E together with nonemptiness, closedness, and convexity. Empty domains are therefore excluded; boundedness, compactness, interior, and positive dimension are not required.

The imported project definition chooses a point using the complete-convex nearest-distance existence interface. Write P_V for that chosen projection. This identifies the operation intended by its actual definition; it is not verification of the imported existence theorem or of any target's proof.

For any real η, vector stream g:N→E and arbitrary initial x0∈E, the four actual packet definitions are:
\[
A_{\eta,g}(x)=P_V(x-\eta g),\qquad
X_0=x_0,\quad X_{t+1}=P_V(X_t-\eta g_t),\qquad
p_t=X_{t+1},\qquad
R_T(u)=\sum_{t=0}^{T-1}\langle g_t,p_t-u\rangle.
\]
Here the one-step A uses a single vector g, while the recursion uses g_t. Scalar multiplication is the real vector-space operation. The prediction is the *updated* state, not X_t: p0=P_V(x0−ηg0), and p_t incorporates g_t together with g0,…,g_(t−1). X_t uses only the strict prefix g0,…,g_(t−1). Thus the definitions expose the same-round vector before the scored prediction; they do not express a standard pre-reveal action independent of g_t. For fixed V,η,x0, changing vectors after t does not affect p_t. There is no restriction on how a supplied stream, parameter, or initial state was chosen in an external setting; the prefix theorem holds those parameters fixed.

The definition R is signed, unnormalized fixed-comparator cumulative linear regret. It is neither an infimum over comparators nor expected regret. No probability law, gradients of nonlinear functions, gradient norm bound, sequence-adaptation premise, or stochastic independence occurs. At T=0 the sum is empty, R0=0 and XT=x0. At T>0, XT=p_(T−1). The definitions permit η=0 and negative η; only specific bound/minimizer types impose positivity. Real division is totalized, but the types with 2η denominators require η>0.

## 1. advance_sharp_bound

For every positive step size and every feasible comparator u, one projected update from any ambient x has linear loss difference at most the decrease in squared comparator distance minus its squared movement, divided by 2η.

\[
\forall V,\ \forall\eta>0,\ \forall g,x,u\in E,\quad
u\in V\Longrightarrow
\langle g,A-u\rangle
\le\frac{\|x-u\|^2-\|A-u\|^2-\|A-x\|^2}{2\eta},
\quad A=P_V(x-\eta g).
\]

1. **Objects:** One domain, positive real η, ambient vectors g,x,u and the actual update A.
2. **Quantifiers/order:** Universal E and structures, V,η and its positivity proof, then g,x,u, with feasibility of u. No existential choice of update is in the conclusion.
3. **Assumptions:** Domain's bundled conditions, completeness, η>0, and u∈V. x need not lie in V; g is arbitrary.
4. **Conclusion:** The displayed inequality, with loss evaluated at updated A and both final-distance and movement squares subtracted.
5. **Constants/boundaries:** Denominator 2η is strictly positive; η=0/negative cases excluded. g=0, x=u, singleton V, and zero-dimensional E are not excluded. No division by a vector norm.
6. **Information:** A reads the same g that is scored. Deterministic single-step statement, no future or probability parameters.
7. **Not established by the header:** The inequality has no supplied proof. No strict-past loss guarantee, regret nonnegativity, or gradient-norm penalty is asserted.

## 2. advance_proximal_minimizer

For arbitrary ambient g,x and real offset b, the actual projected update with positive η is feasible and minimizes the affine loss plus squared distance to x over V.

\[
\forall V:\mathrm{Domain}(E),\ \forall\eta\in\mathbb R,\ \eta>0\Rightarrow
\forall g,x\in E,\ \forall b\in\mathbb R,\quad
A\in V\ \land\
\forall u\in V,\
\langle g,A\rangle+b+\frac{\|A-x\|^2}{2\eta}
\le \langle g,u\rangle+b+\frac{\|u-x\|^2}{2\eta},
\quad A=P_V(x-\eta g).
\]
More precisely, the binders are \(V:\mathrm{Domain}(E),\ \eta:\mathbb R,\ \eta>0,\ g,x:E,\ b:\mathbb R\).

1. **Objects:** Actual A and objective F(v)=⟨g,v⟩+b+||v−x||²/(2η).
2. **Quantifiers/order:** V,η>0,g,x,b first; conclusion is membership conjoined with every feasible u's comparison. The same b and x occur on both sides.
3. **Assumptions:** Domain and complete-space structure plus η>0. No x∈V assumption, sign restriction on b, or bound on g.
4. **Conclusion:** Feasibility and attainment of a global constrained minimum by this defined A; not merely an unspecified minimizer's existence.
5. **Constants/boundaries:** Same strictly positive 2η; arbitrary offset b cancels in comparisons. Zero vector or singleton-domain cases remain allowed.
6. **Information:** A depends on V,η,g,x and not on b or comparator u. No observation or randomness.
7. **Not established by the header:** Minimization is proposed, not proved here. The type does not assert uniqueness, an algorithm for computing the projection, or unconstrained minimization.

## 3. prediction_mem

Every defined prediction lies in V, for arbitrary real step size and arbitrary initial ambient point.

\[
\forall V,\eta\in\mathbb R,g:\mathbb N\to E,x_0\in E,t\in\mathbb N,\quad p_t\in V.
\]

1. **Objects:** The exact recursion and prediction p_t= X_(t+1).
2. **Quantifiers/order:** E/structures, V,η,g,x0,t universally quantified in that order.
3. **Assumptions:** Only type and bundled domain conditions; no step-size positivity and no initial feasibility premise.
4. **Conclusion:** Feasibility of the post-update prediction at each t.
5. **Constants/boundaries:** At t=0 the prediction is already projected; the claim is not x0∈V. η=0 or negative η is included. No horizon restriction.
6. **Information:** p_t incorporates g_t. No claim of strict-past-only prediction is made.
7. **Not established by the header:** Feasibility is a proposed theorem; arbitrary X0 feasibility and any regret inequality are not conclusions of this header.

## 4. prediction_prefix

Two vector streams agreeing through and including t produce the same time-t prediction when V,η,x0 are identical.

\[
\forall V,\eta,g,g',x_0,t,\quad
\bigl[\forall s\in\mathbb N,\ s\le t\Rightarrow g_s=g'_s\bigr]
\Rightarrow p_t(V,\eta,g,x_0)=p_t(V,\eta,g',x_0).
\]

1. **Objects:** Two runs of the actual recursion, with streams g,g' and all other parameters shared.
2. **Quantifiers/order:** Universal V,η,g,g',x0,t followed by agreement of every s≤t; equality is the conclusion.
3. **Assumptions:** Inclusive-prefix agreement. η is arbitrary; no feasibility assumption on x0.
4. **Conclusion:** Equal time-t updated predictions.
5. **Constants/boundaries:** At t=0 agreement requires g0=g'0; the premise is not empty. No equality required at indices greater than t.
6. **Information:** Inclusive current-vector dependence and no dependence on subsequent vector coordinates for fixed parameters. The premise is s≤t, not s<t.
7. **Not established by the header:** The causal equality is proposed, not proved. It neither claims agreement on strict past suffices nor constrains external selection of x0 or η using a full stream.

## 5. regret_eq_loss_difference

For any scalar-offset sequence b, regret equals the sum of affine losses at the actual updated predictions minus losses at one fixed comparator u.

\[
\forall V,\eta,g,b,x_0,u,T,\quad
R_T(u)=\sum_{t<T}
\left[(\langle g_t,p_t\rangle+b_t)-(\langle g_t,u\rangle+b_t)\right].
\]

1. **Objects:** Stream g:N→E, offset stream b:N→R, actual predictions, ambient fixed u and natural horizon T.
2. **Quantifiers/order:** V,η,g,b,x0,u,T are all universal; u is fixed across the entire sum.
3. **Assumptions:** No η positivity, no u∈V, no x0∈V, and no restriction on either stream.
4. **Conclusion:** Exact equality of the defined signed linear regret and the affine per-round loss differences.
5. **Constants/boundaries:** Sum range T includes 0,…,T−1. T=0 makes both sides zero. Same b_t on both sides of each round; no division or normalization.
6. **Information:** b does not enter the prediction recursion. Predictions use the same g_t as the scored round, not a different trajectory.
7. **Not established by the header:** The equality has no supplied proof; no minimization over u, feasibility claim, or bound follows solely from this header.

## 6. regret_sharp_bound

For each feasible fixed comparator and positive fixed η, cumulative regret of the actual run is at most the initial squared distance divided by 2η, minus both terminal squared distance and the sum of squared update movements with the same denominator.

\[
\forall V,\eta>0,g,x_0,u,T,\quad u\in V\Longrightarrow
R_T(u)\le
\frac{\|x_0-u\|^2}{2\eta}
-\frac{\|X_T-u\|^2}{2\eta}
-\frac{\sum_{t<T}\|p_t-X_t\|^2}{2\eta}.
\]

1. **Objects:** One actual constant-step recursion, its initial state, terminal state XT, updated predictions and fixed comparator.
2. **Quantifiers/order:** Universal V,η>0,g,x0,u,T, then comparator feasibility; the same run appears in all terms.
3. **Assumptions:** η>0 and u∈V, besides domain/space structure. No x0 feasibility, vector magnitude bound, bounded domain, or positive-horizon premise.
4. **Conclusion:** Signed cumulative bound retaining both negative residual terms exactly.
5. **Constants/boundaries:** At T=0, XT=x0 and the movement sum is empty, so the proposed inequality is 0≤0. For T>0 terminal XT is the last scored prediction p_(T−1), not p_T. Fixed denominator 2η for all terms; movement is X_(t+1)−X_t.
6. **Information:** Same-round vectors determine scored predictions. η is constant across the run; no expectation or adaptive step-size sequence.
7. **Not established by the header:** Telescoping and the inequality are unproved in this packet. No ordinary limit, one-sided asymptotic condition, or uniform bound independent of x0,u,η is asserted.

## 7. regret_source_bound

With the same hypotheses and same actual run, cumulative regret is bounded by initial squared distance divided by 2η minus the squared-movement sum divided by 2η; this type omits the terminal-distance subtraction.

\[
\forall V,\eta>0,g,x_0,u,T,\quad u\in V\Longrightarrow
R_T(u)\le
\frac{\|x_0-u\|^2}{2\eta}
-\frac{\sum_{t<T}\|p_t-X_t\|^2}{2\eta}.
\]

1. **Objects:** The same definitions of V,η,g,x0,XT,p_t and R, with one fixed feasible u.
2. **Quantifiers/order:** Universal V,η>0,g,x0,u,T and feasibility premise. No existential parameter tuning or alternative predictor.
3. **Assumptions:** Complete inner-product space and bundled domain, η>0, u∈V. Arbitrary initial point and vector stream.
4. **Conclusion:** The displayed finite, unnormalized signed regret upper bound, retaining movement subtraction but not terminal-distance subtraction.
5. **Constants/boundaries:** T=0 gives 0≤||x0−u||²/(2η), rather than the exact zero right side of the preceding target. All T∈N are included; all denominators are positive.
6. **Information:** Same inclusive-current-vector prediction and fixed-step run. No probability, expectation, norm bound, or information restriction beyond the actual recursion.
7. **Not established by the header:** The name does not identify or certify any external source. Neither this inequality nor its derivation from the preceding stronger-looking type has been proved in this packet.

## Completeness and unresolved questions

All seven proposed headers and all four supplied definitions have been reconstructed. The permitted imported Domain and project definitions resolve the otherwise unspecified carrier assumptions and projection operation. No additional type/semantic context is required for this reading. The index packet hash agrees with the raw packet bytes; raw before/after bindings are recorded separately.

The types propose feasibility, minimization, prefix invariance, affine-loss identity and finite bounds. Their appearance as headers does not establish any of these propositions or dependencies between them. Nothing in this packet supplies theorem bodies, typechecking evidence, a standard pre-current-observation online protocol, source fidelity, or chapter acceptance. No such verdict is given.

